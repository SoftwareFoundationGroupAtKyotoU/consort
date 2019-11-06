open Ast

open Std
open Std.StateMonad
open SimpleTypes
    
module SM = StringMap
module SS = StringSet
module P = Paths

module OI = OwnershipInference
module RT = RefinementTypes

type concr_ap = P.concr_ap

type z3_types =
  | ZBool
  | ZInt

type flow =
  | Havoc of P.concr_ap
  | Copy of P.concr_ap * P.concr_ap
  | Const of P.concr_ap * int

type relation = string * (P.concr_ap * z3_types) list

type concr_arg = P.concr_ap RT.rel_imm

type clause =
  | PRelation of relation * ((P.concr_ap * concr_arg) list)
  | Relation of P.concr_ap RT.refinement_rel
  | NamedRel of string * (concr_arg list)

type ctxt = {
  relations: relation list;
  impl: (clause list * clause) list;
  o_hints: float OI.ownership_ops;
  fenv: (relation * relation * SimpleTypes.funtyp) StringMap.t;
  curr_fun : string option;
  let_types: SimpleTypes.r_typ Std.IntMap.t
}

let mk_flow ~havoc in_ap out_ap =
    if havoc then
      Havoc out_ap
    else
      Copy (in_ap,out_ap)

let%lq split_mem sloc in_ap ctxt =
  OI.SplitMap.find (sloc,in_ap) ctxt.o_hints.OI.splits

let%lq get_function_type f_name ctxt =
  let (_,_,to_ret) = StringMap.find f_name ctxt.fenv in
  to_ret

let%lq get_in_relation f_name ctxt =
  let (ir,_,_) = StringMap.find f_name ctxt.fenv in
  ir

let%lq get_out_relation f_name ctxt =
  let (_,o_rel,_) = StringMap.find f_name ctxt.fenv in
  o_rel

let%lm add_assert assert_cond curr_relation  ctxt =
  let lift_to_imm = function
    | IVar v -> RT.RAp (P.var v)
    | IInt i -> RT.RConst i
  in
  let relation = Relation RT.({
        rel_op1 = RImm (lift_to_imm assert_cond.rop1);
        rel_cond = assert_cond.cond;
        rel_op2 = lift_to_imm assert_cond.rop2
      }) in
  let ante = [ PRelation (curr_relation,[]) ] in
  { ctxt with impl = (ante,relation)::ctxt.impl }

let path_simple_type tyenv path =
  let rec loop path k =
    match path with
    | `AVar v -> k @@ List.assoc v tyenv
    | `ADeref p ->
      loop p (function
        | `Ref t -> k t
        | _ -> assert false
        )
    | `AProj (p,i) ->
      loop p (function
        | `Tuple tl -> List.nth tl i
        | _ -> assert false
        )
    | _ -> failwith "Not supported"
  in
  loop path (fun i -> i)

let to_havoc d = Printf.sprintf "havoc!%d!%s" d

let%lm add_implication ante conseq ctxt =
  {ctxt with impl = (ante,conseq)::ctxt.impl }

let%lm add_relation_flow ?(pre=[]) subst in_rel out_rel ctxt =
  let lifted_subst = List.mapi (fun i elem ->
      match elem with
      | Havoc p -> (p,RT.RAp (P.map_root (to_havoc i) p))
      | Const (p,c) -> (p,RT.RConst c)
      | Copy (p1,p2) -> (p2,RT.RAp p1)
    ) subst in
  let ante = PRelation (in_rel,[])::pre in
  let conseq = PRelation (out_rel,lifted_subst) in
  {
    ctxt with impl = ((ante,conseq)::ctxt.impl)
  }

let type_to_paths ?(pre=false) root ty =
  let rec loop under_ref acc p = function
    | `Int -> p::(if under_ref && pre then (P.pre p)::acc else acc)
    | `Ref t -> loop true acc (P.deref p) t
    | `Tuple tl ->
      fold_lefti (fun i acc t ->
          loop under_ref acc (P.t_ind p i) t
        ) acc tl
    | _ -> assert false
  in
  loop false [] root ty

let default_hook _ _ acc = acc
    
let do_flow ?(hook=default_hook) ~sloc in_ap out_ap ty =
  let rec loop (in_ap,ih) (out_ap,oh) ty acc =
      match ty with
      | `Int ->
        return @@ (mk_flow ~havoc:ih in_ap in_ap)::(mk_flow ~havoc:oh in_ap out_ap)::(hook (in_ap,ih) (out_ap,oh) acc)
      | `Tuple tl ->
        let susp_i = List.mapi (fun i s_ty ->
            loop ((P.t_ind in_ap i),ih)
              ((P.t_ind out_ap i),oh) s_ty) tl in
        mfold_left (fun acc e ->
          e acc
        ) acc susp_i
      | `Ref r ->
        let%bind (o1,o2) = split_mem sloc in_ap in
        loop (P.deref in_ap, o1 = 0.0) (P.deref out_ap, o2 = 0.0) r acc
      | `Array _
      | `TVar _
      | `Mu _ -> assert false
  in
  loop (in_ap, false) (out_ap, false) ty []
  
let apply_flow ~tyenv ~sloc in_path out_path in_rel out_relation =
  let ty = path_simple_type tyenv in_path in
  let%bind acc = do_flow ~sloc in_path out_path ty in
  add_relation_flow acc in_rel out_relation

let apply_identity_flow ?pre = add_relation_flow ?pre []

let const_assign lhs const =
  add_relation_flow [ Const (lhs,const) ]

let vderef v = P.deref @@ P.var v

let apply_patt_type ~e_id patt path ty in_rel out_rel =
  let rec loop patt path ty acc =
    match patt,ty with
    | PNone,_ -> return acc
    | PVar v,`Int ->
      return @@ (mk_flow ~havoc:false path (P.var v))::(mk_flow ~havoc:false path path)::acc
    | PVar v,ty -> do_flow ~sloc:(SBind e_id) path (P.var v) ty
    | PTuple t,`Tuple tl ->
      let ind_types = List.mapi (fun i t -> (i,t)) tl in
      mfold_left2 (fun acc p (i,t) ->
        loop p (P.t_ind path i) t acc
      ) acc t ind_types
    | PTuple _,_ -> assert false
  in
  let%bind flows = loop patt path ty [] in
  add_relation_flow flows in_rel out_rel

(* This will fail miserably in the presence of bifs ... *)

type _ pre_flag =
  | Pre : ((P.concr_ap * concr_arg) list * (P.concr_ap * concr_arg) list) pre_flag
  | NoPre : (P.concr_ap * concr_arg) list pre_flag

let subst_for_type : type a.P.concr_ap -> P.concr_ap -> SimpleTypes.r_typ -> a pre_flag -> a -> a =
  fun actual formal ty ->
    let rec loop under_ref actual_ap formal_ap ty =
      match ty with
      | `Int ->
        let bind = (formal_ap,RT.RAp actual_ap) in
        let (ret : a pre_flag -> a -> a) = function
          | Pre -> (fun (out_bind,pre_bind) ->
              let out_bind = bind::out_bind in
              if under_ref then
                let pre_ap = P.pre actual_ap in
                let pre_bind = (actual_ap,RT.RAp pre_ap)::pre_bind in
                let out_bind = (P.pre formal_ap,RT.RAp pre_ap)::out_bind in
                (out_bind,pre_bind)
              else
                (out_bind,pre_bind)
            )
          | NoPre -> (fun out_bind ->
              bind::out_bind
            )
        in
        ret
      | `Tuple tl ->
        fold_lefti (fun i cont t ->
            (fun p acc ->
              let d = cont p acc in
              loop under_ref (P.t_ind actual_ap i) (P.t_ind formal_ap i) t p d
            )
          ) (fun _ acc -> acc) tl
      | `Ref t -> loop true (P.deref actual_ap) (P.deref formal_ap) t
      | _ -> assert false
    in
    loop false actual formal ty

let bind_arg ~e_id (in_bind,out_bind,pre_bind) actual formal ty =
  let (out_bind,pre_bind) = subst_for_type actual formal ty Pre (out_bind,pre_bind) in
  let rec under_ref = function
    | `ADeref _ -> true
    | `AVar _
    | `APre _
    | `ARet -> false
    | `AProj (ap,_) -> under_ref ap
    | _ -> assert false
  in
  let propagate_pre (in_ap,_) (out_ap,_) acc =
    if under_ref in_ap then
      Copy (in_ap,P.pre out_ap)::acc
    else
      acc
  in
  let%bind in_bind' = do_flow ~hook:propagate_pre ~sloc:(SCall e_id) actual formal ty in
  return (in_bind' @ in_bind,out_bind,pre_bind)

let return_bind out_patt ret_type =
  let rec loop acc out_patt ret_path ty =
    match out_patt,ty with
    | PVar v,_ -> subst_for_type ret_path (P.var v) ty NoPre acc
    | PTuple pl,`Tuple tl ->
      fold_left2i (fun i acc p t ->
          loop acc p (P.t_ind ret_path i) t
        ) acc pl tl
    | PTuple _,_ -> assert false
    | PNone,_ -> acc
  in
  loop [] out_patt `ARet ret_type

(* switch on whether we find the bif in a special summary table ... ? *)
let bind_args ~e_id out_patt call_expr curr_rel body_rel =
  let callee = call_expr.callee in
  let%bind callee_type = get_function_type callee in
  let%bind in_rel = get_in_relation callee in
  let%bind out_rel = get_out_relation callee in
  let args = call_expr.arg_names in
  let%bind (in_bindings,out_bindings,pre_bindings) = fold_left2i (fun i acc arg_name arg_ty ->
      let%bind acc = acc in
      bind_arg ~e_id acc (P.var arg_name) (P.arg i) arg_ty
    ) (return ([],[],[])) args callee_type.arg_types in
  let return_bindings = return_bind out_patt callee_type.ret_type in

  begin%m
      add_relation_flow in_bindings curr_rel in_rel;
       add_implication [
         PRelation (curr_rel,pre_bindings);
         PRelation (out_rel,out_bindings)
       ] @@ PRelation (body_rel,return_bindings)
  end

let apply_patt ~e_id tyenv patt rhs =
  match patt,rhs with
  | PNone,_ -> apply_identity_flow ?pre:None
  | _,Var s ->
    let path = P.var s in
    apply_patt_type ~e_id patt path @@ path_simple_type tyenv path
  | PVar s,Const n -> add_relation_flow [ Const (P.var s,n) ]

  | PVar s,Mkref RNone ->
    add_relation_flow [ Havoc (vderef s) ]
  | PVar s,Mkref (RInt n)  ->
    add_relation_flow [ Const (vderef s,n) ]
  | PVar s,Mkref (RVar v) ->
    apply_flow ~tyenv ~sloc:(OI.SBind e_id) (P.var v) (vderef s)

  | _,Deref v ->
    apply_patt_type ~e_id patt (vderef v) @@ path_simple_type tyenv (vderef v)
        
  | PVar t,Tuple tl ->
    let tup_root = P.var t in
    let susp = List.mapi (fun i r acc ->
        let tgt_ap = P.t_ind tup_root i in
        match r with
        | RNone -> return @@ (Havoc tgt_ap)::acc
        | RInt n -> return @@ (Const (tgt_ap,n))::acc
        | RVar v ->
          let in_typ = path_simple_type tyenv @@ P.var v in
          let%bind acc' = do_flow ~sloc:(STuple (e_id,i)) (P.var v) tgt_ap in_typ in
          return @@ acc' @ acc
      ) tl
    in
    (fun i o ->
      let%bind flows = mfold_left (fun acc e ->
          e acc
        ) [] susp in
      add_relation_flow flows i o)

  | PTuple _,Tuple _ -> assert false
  | _,Call c -> bind_args ~e_id patt c
  | PTuple _,_ -> assert false
  | PVar v,Nondet None -> add_relation_flow [ Havoc (P.var v) ]
  | PVar _,Nondet (Some _) -> assert false
    
  (* not yet implemented *)
  | _,MkArray _
  | _,Read _
  | _,LengthOf _
  | _,Null -> assert false

let relation_name ((e_id,_),expr) ctxt =
  let prefix = Printf.sprintf "%s-%d-" (Option.value ~default:"main-fn" ctxt.curr_fun) e_id in
  let kind =
    match expr with
    | Let _ -> "let"
    | Seq _ -> "seq"
    | Assign _ -> "assign"
    | Update _ -> "update"
    | Assert _ -> "assert"
    | Alias _ -> "alias"
    | NCond _ -> "ifnull"
    | Cond _ -> "ifz"
    | EVar _ -> "var"
    | EAnnot _ -> "$gamma"
  in
  prefix ^ kind

let fresh_relation_for curr_relation k ctxt =
  let rel = relation_name k ctxt in
  let (_,args) = curr_relation in
  let to_ret = (rel,args) in
  { ctxt with relations = to_ret::ctxt.relations },to_ret

let to_cont k = (Some k),None

let fresh_bind_relation e_id (relation,tyenv) patt k ctxt =
  let (_,curr_args) = relation in
  let bound_type = Std.IntMap.find e_id ctxt.let_types in
  let rec destruct_loop (tyenv,args) patt ty =
    match patt,ty with
    | PVar v,ty ->
      let ty_env = (v,ty)::tyenv in
      let paths = List.rev @@ type_to_paths (P.var v) ty in
      let args = (List.map (fun p -> (p,ZInt)) paths) @ args in
      (ty_env,args)
    | PTuple pl,`Tuple tl ->
      List.fold_left2 destruct_loop (tyenv,args) pl tl
    | PTuple _,_ -> assert false
    | PNone,_ -> (tyenv,args)
  in
  let (tyenv',args) = destruct_loop (tyenv,[]) patt bound_type in
  let new_args = curr_args @ (List.rev args) in
  let name = relation_name k ctxt in
  let relation = (name, new_args) in
  { ctxt with relations = relation::ctxt.relations },(relation,tyenv')

let rec process_expr ((relation,tyenv) as st) continuation ((e_id,_),e) =
  match e with
  | EVar v ->
    begin
      match continuation with
      | (Some out_relation),None ->
        (* intra procedural successor *)
        apply_identity_flow relation out_relation
          
      (* should only happen at the main function *)                
      | None,None ->
        return ()

      (* tail position *)
      | (Some out_relation),Some ret_var ->
        apply_flow ~tyenv ~sloc:(SRet e_id) (P.var v) ret_var relation out_relation
      | None, Some _ -> assert false
    end
    
  | Seq (e1, e2) ->
    let%bind e2_rel = fresh_relation_for relation e2 in
    let%bind () = process_expr st (to_cont e2_rel) e1 in
    process_expr (e2_rel,tyenv) continuation e2
      
  | Assign (lhs,IInt i,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    const_assign (P.deref @@ P.var lhs) i relation k_rel >> process_expr (k_rel,tyenv) continuation k
      
  | Assign (lhs,IVar rhs,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    apply_flow ~tyenv ~sloc:(SBind e_id) (P.var rhs) (P.deref @@ P.var lhs) relation k_rel >> process_expr (k_rel,tyenv) continuation k
      
  | Update _ -> assert false
  | Cond (v,e1,e2) ->
    let%bind e1_rel = fresh_relation_for relation e1 in
    let%bind e2_rel = fresh_relation_for relation e2 in
    
    let mk_pre rel_cond = Relation RT.({
        rel_op1 = RImm (RAp (P.var v)); rel_cond; rel_op2 = RConst 0 
        })
    in
    begin%m
        apply_identity_flow ~pre:[ mk_pre "=" ] relation e1_rel;
         process_expr (e1_rel,tyenv) continuation e1;
         apply_identity_flow ~pre:[ mk_pre "!=" ] relation e2_rel;
         process_expr (e2_rel,tyenv) continuation e2
    end
  | NCond _ -> assert false
    
  | Let (patt,rhs,k) ->
    let%bind k_rel,tyenv' = fresh_bind_relation e_id st patt k in
    apply_patt ~e_id tyenv patt rhs relation k_rel >> process_expr (k_rel,tyenv') continuation k
      
  | EAnnot _ -> assert false
    
  | Assert (assrt, k) ->
    let%bind k_rel = fresh_relation_for relation k in
    add_assert assrt relation >>
    apply_identity_flow relation k_rel >>
    process_expr (k_rel,tyenv) continuation k
      
  | Alias _ (* (lhs,s_ap,k) *) -> assert false

let analyze_function fn ctxt =
  let ((in_nm,in_args),(out_nm,out_args),fn_type) = StringMap.find fn.name ctxt.fenv in
  let initial_env = List.map2 (fun v ty ->
      (v,ty)
    ) fn.args fn_type.arg_types in
  let arg_mapping = fold_lefti (fun i acc nm ->
      StringMap.add (P.arg_name i) nm acc
    ) StringMap.empty fn.args in
  let map_args = List.map (fun (p,ty) ->
      let p' = Paths.map_root (fun t ->
          StringMap.find t arg_mapping
        ) p
      in
      (p',ty)
    )
  in
  let mapped_in_args = map_args in_args in
  let mapped_out_args = map_args out_args in
  let cont = (Some (out_nm, mapped_out_args)),Some `ARet in
  let ctxt,() = process_expr ((in_nm,mapped_in_args),initial_env) cont fn.body {ctxt with curr_fun = Some fn.name } in
  ctxt

let analyze_main start_rel main ctxt =
  let ctxt,() = process_expr (start_rel,[]) (None,None) main ctxt in
  ctxt

let infer (simple_theta,side_results) o_hints (fns,main) =
  let (fenv,relations) = StringMap.fold (fun name ty (theta,rel) ->
      let arg_paths =
        List.mapi (fun i arg_t ->
          type_to_paths ~pre:true (P.arg i) arg_t
        ) ty.arg_types
      in
      let in_rel_types = List.map (fun p -> (p,ZInt)) @@ List.concat arg_paths in
      let ret_rel = type_to_paths `ARet ty.ret_type |> List.map (fun p -> (p,ZInt)) in
      let out_rel_types = in_rel_types @ ret_rel in
      let in_rel = (name ^ "-in", in_rel_types) in
      let out_rel = (name ^ "-out", out_rel_types) in
      let ftype = (in_rel,out_rel,ty) in
      (StringMap.add name ftype theta,in_rel::out_rel::rel)
    ) simple_theta (StringMap.empty, []) in
  let entry_relation = ("program-start", []) in
  let relations = entry_relation::relations in
  let empty_ctxt = {
    relations;
    impl = [ ([],PRelation (entry_relation,[])) ];
    o_hints;
    curr_fun = None;
    let_types = side_results.SimpleChecker.SideAnalysis.let_types;
    fenv
  } in
  let ctxt = List.fold_left (fun ctxt fn ->
      analyze_function fn ctxt
    ) empty_ctxt fns in
  let ctxt = analyze_main entry_relation main { ctxt with curr_fun = None } in
  (ctxt.relations,ctxt.impl)

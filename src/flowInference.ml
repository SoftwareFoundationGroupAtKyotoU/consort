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

let print_relation (str, l) = 
  let _ = Printf.printf "relation: %s " str  in
  let _ = 
    List.iter (fun (c,_) -> 
      Printf.printf "%s " (P.to_z3_ident c)) l
  in print_newline()



type concr_arg = P.concr_ap RT.rel_imm

type clause =
  | PRelation of relation * ((P.concr_ap * concr_arg) list) * int option
  | Relation of (concr_arg,concr_arg) RT.relation
  | NamedRel of string * (concr_arg list)

type ctxt = {
  relations: relation list;
  impl: (clause list * clause) list;
  o_hints: float OI.ownership_ops;
  fenv: (relation * relation * SimpleTypes.funtyp) SM.t;
  curr_fun : string option;
  let_types: SimpleTypes.r_typ Std.IntMap.t;
  bif_types : RefinementTypes.funtype SM.t;
  havoc_set : P.PathSet.t;
}

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

let%lq copy_state ctxt = ctxt

let%lm set_havoc_state havoc_state ctxt = { ctxt with havoc_set = havoc_state }

let%lq get_havoc_state ctxt = ctxt.havoc_set

let mk_relation lhs op rhs = RT.({
    rel_op1 = lhs;
    rel_cond = op;
    rel_op2 = rhs
  })

let rel k = Relation k

let%lm add_assert op1 cond op2 curr_relation ctxt =
  let ante = [ PRelation (curr_relation,[],None) ] in
  let relation = rel @@ mk_relation op1 cond op2 in
  { ctxt with impl = (ante,relation)::ctxt.impl }

let add_assert_cond assert_cond curr_relation =
  let lift_to_imm = function
    | IVar v -> RT.RAp (P.var v)
    | IInt i -> RT.RConst i
  in
  add_assert
    (lift_to_imm assert_cond.rop1)
    assert_cond.cond
    (lift_to_imm assert_cond.rop2)
    curr_relation
let rec havoc_oracle ctxt ml = function
  | `ADeref ap ->
    let o = OI.GenMap.find (ml,ap) ctxt.o_hints.OI.gen in
    o = 0.0
  | `ARet _
  | `AVar _ -> false

  | `ALen ap
  | `AInd ap
  | `AElem ap
  | `AProj (ap,_) -> havoc_oracle ctxt ml ap

let%lq split_oracle sl ctxt =
  let from_path p =
    let (f1,f2) = OI.SplitMap.find (sl,p) ctxt.o_hints.OI.splits in
    (f1 = 0.0, f2 = 0.0)
  in
  let rec loop = function
    | `ARet _, _
    | _,`AVar _
    | _,`ARet _
    | `AVar _,_ -> (false,false)
    | (`AInd p),`AInd _
    | (`AElem p),`AElem _
    | (`ADeref p),(`ADeref _) -> from_path p
    | (`ALen p1),(`ALen p2)
    | `AProj (p1,_),`AProj (p2,_) -> loop (p1,p2)
    | a,b -> failwith @@ Printf.sprintf "Incompatible paths %s => %s"
          (P.to_z3_ident a) (P.to_z3_ident b)
  in
  fun src dst -> loop (src,dst)

let%lq gen_for_alias e_id ctxt =
  havoc_oracle ctxt (OI.MAlias e_id)

let%lq gen_oracle ml ctxt =
  havoc_oracle ctxt ml

let rec lift_refinement ?(map=Fun.id) ?nu_arg =
  let lift_symbolic_ap = function
    | `Sym _ -> assert false
    | #P.concr_ap as cap -> map cap
  in
  let lift_symbolic_imm = function
    | RT.RConst i -> RT.RConst i
    | RT.RAp p -> RT.RAp (lift_symbolic_ap p)
  in
  RT.(function
  | Top -> []
  | And (r1, r2) -> lift_refinement ~map ?nu_arg r1 @ lift_refinement ~map ?nu_arg r2
  | ConstEq i ->
    [ rel @@ mk_relation (RAp (Option.get nu_arg)) "=" (RConst i) ]
  | Relation r when r.rel_op1 = Nu ->
    [ rel { r with rel_op1 = RAp (Option.get nu_arg); rel_op2 = lift_symbolic_imm r.rel_op2 } ]
  | Relation ({ rel_op1 = RImm i; _ } as r) ->
    [ rel { r with rel_op1 = (lift_symbolic_imm i); rel_op2 = lift_symbolic_imm r.rel_op2 } ]
  | NamedPred (nm,sym_names) ->
    let nu_arg = Option.get nu_arg in
    let named_args = List.map lift_symbolic_ap sym_names in
    let val_args = List.map (fun l -> RT.RAp l) @@ nu_arg::named_args in
    [ NamedRel (nm,val_args) ]
  | _ -> failwith "Refinement form not supported")

let path_simple_type tyenv path =
  let rec loop path k =
    match path with
    | `AVar (v,false,false) -> k @@ List.assoc v tyenv
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

let havoc_ap d = P.map_root (to_havoc d)

(* we effect a copy from a to b by replacing b with a *)
let copy_to_flow (src,dst) =
  (dst, RT.RAp src)

let%lm add_implication ante conseq ctxt =
  {ctxt with impl = (ante,conseq)::ctxt.impl }

let%lm add_relation_flow ?out_ctxt ?(pre=[]) subst in_rel out_rel ctxt =
  let lifted_subst = List.mapi (fun i elem ->
      match elem with
      | Havoc p -> (p,RT.RAp (havoc_ap i p))
      | Const (p,c) -> (p,RT.RConst c)
      | Copy (p1,p2) -> (p2,RT.RAp p1)
    ) subst in
  let ante = PRelation (in_rel,[],None)::pre in
  let conseq = PRelation (out_rel,lifted_subst,out_ctxt) in
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
    | `Array `Int ->
      (`ALen p)::(`AInd p)::(`AElem p)::acc
    | `Mu _ | `TVar _ -> assert false
  in
  loop false [] root ty

let compute_copies in_ap out_ap ty =
  let rec loop in_ap out_ap ty acc =
    match ty with
    | `Int -> (in_ap, out_ap)::acc
    | `Ref t -> loop (P.deref in_ap) (P.deref out_ap) t acc
    | `Tuple tl ->
        fold_lefti (fun i acc t ->
          loop (P.t_ind in_ap i) (P.t_ind out_ap i) t acc
        ) acc tl
    | `Array `Int ->
      (P.ind in_ap,P.ind out_ap)::(P.len in_ap, P.len out_ap)::(P.elem in_ap,P.elem out_ap)::acc
    | _ -> assert false
  in
  loop in_ap out_ap ty []


let compute_patt_copies path patt ty =
  let rec loop patt path ty acc =
    match patt,ty with
    | PNone,_ -> acc
    | PVar v,`Int ->
      (path,P.var v)::acc
    | PVar v,ty ->
      (compute_copies path (P.var v) ty) @ acc
    | PTuple t,`Tuple tl ->
      fold_left2i (fun i acc p t ->
          loop p (P.t_ind path i) t acc
        ) acc t tl
    | PTuple _,_ -> assert false
  in
  loop patt path ty []

let compute_flows ~sl copies =
  let%bind split_oracle = split_oracle sl in
  ListMonad.bind (fun (src,dst) ->
    let (f1,f2) = split_oracle src dst in
    let src_flow =
      if f1 then
        Havoc src
      else Copy(src,src)
    in
    let dst_flow =
      if f2 then
        Havoc dst
      else
        Copy(src,dst)
    in
    [src_flow;dst_flow]
  ) copies
  |> List.fold_left (fun (havoc,stable,flows) flow ->
      match flow with
      | Havoc s ->
        let () = assert (not (P.PathSet.mem s stable)) in (P.PathSet.add s havoc,stable,flow::flows)
      | Copy (s,d) ->
        if s <> d then
          let () = assert (not (P.PathSet.mem d havoc)) in (havoc,P.PathSet.add d stable,flow::flows)
        else
          (havoc,stable,flow::flows)
      | Const _ -> assert false
    ) (P.PathSet.empty,P.PathSet.empty,[])
  |> return

let%lm apply_copies ~havoc:havoc_flag ~sl ?(flows=[]) copies in_rel out_rel ctxt =
  let ctxt,(havoc,stable,copy_flows) = compute_flows ~sl copies ctxt in
  let havoc_set = ctxt.havoc_set in
  let havoc_set = P.PathSet.union havoc @@ P.PathSet.diff havoc_set stable in
  let flows = flows @ copy_flows @ begin
      if havoc_flag then
        P.PathSet.elements havoc_set |> List.map (fun p -> Havoc p)
      else
        []
    end
  in
  let ctxt,() = add_relation_flow flows in_rel out_rel ctxt in
  { ctxt with havoc_set }

let apply_identity_flow ?pre = add_relation_flow ?pre []

let const_assign lhs const in_rel out_rel =
  let%bind havoc_state = get_havoc_state in
  let flows = P.PathSet.elements havoc_state |>
      List.fold_left (fun acc p ->
        Havoc p::acc
      ) [ Const (lhs,const) ]
  in
  add_relation_flow flows in_rel out_rel

let vderef v = P.deref @@ P.var v

let rec is_pre_path = function
  | `ADeref _ -> true
  | `AInd _
  | `AElem _
  | `AVar _
  | `APre _ -> false
  | `ALen p
  | `AProj (p,_) -> is_pre_path p
  | `ARet _ -> assert false (* impossible? *)

let bind_arg ~fn ~e_id (havoc,stable,in_bind,out_bind,pre_bind) actual formal ty =
  let direct_copies = compute_copies actual formal ty in
  let%bind split_oracle = split_oracle (SCall e_id) in
  let id_paths = List.fold_left (fun acc (src,dst) ->
      let (havoc,_) = split_oracle src dst in
      if havoc then
        acc
      else
        P.PathSet.add src acc
    ) P.PathSet.empty direct_copies in
  let in_copies = ListMonad.bind (fun (src,dst) ->
      if is_pre_path dst then
        [ Copy (src,P.pre dst); Copy (src,dst) ]
      else
        [ Copy (src,dst) ]
    ) direct_copies
  in
  
  let%bind havoc_out_oracle = gen_oracle (OI.MOut fn) in

  (* dst is the access path for the argument *)
  let (havoc,stable,out_bind,pre_bind) = List.fold_left (fun (havoc,stable,out_bind,pre_bind) (src,(dst : P.concr_ap)) ->
      let is_pre = is_pre_path src in
      let is_id = P.PathSet.mem src id_paths in
      let havoc_out = havoc_out_oracle dst && (not is_id) in
      let (havoc,stable) =
        if havoc_out then
          (P.PathSet.add src havoc),stable
        else
          havoc,(P.PathSet.add src stable)
      in

      let out_copy = (dst,RT.RAp src) in
      let pre_path = P.map_root (fun p -> p ^ "!call") src in
      let pre_copy = (src,RT.RAp pre_path) in

      (* now compute the out flows, let's do the easy case first *)
      if (not is_pre) && is_id then
        (* Then this is an argument that may not change during execution and for which we do not track
           pre-states then no pre-substitutions are necessary *)
        (havoc,stable,out_copy::out_bind,pre_bind)
      else if (not is_pre) then
        (* this argument may change during execution, and we do not track pre-states. Then create a fresh
           name for the input value (using pre) *)
        (havoc,stable,out_copy::out_bind,pre_copy::pre_bind)
      else if is_pre && is_id then
        (* we track pre states but the argument won't change during execution.
           So constrain the pre-value to be equal to the output argument (do not rename pre) *)
        (havoc,stable,(P.pre dst,RT.RAp src)::out_copy::out_bind,pre_bind)
      else
        (* finally, we track pre states, and the value may change.
           rename the name in the prestate to be pre,
           and rename the pre path in the output *)
        (havoc,stable,(P.pre dst,RT.RAp pre_path)::out_copy::out_bind,pre_copy::pre_bind)
    ) (havoc,stable,out_bind,pre_bind) direct_copies
  in
  return (havoc,stable,in_copies @ in_bind,out_bind, pre_bind)

let bind_return ~fn out_patt ret_type =
  let copies = compute_patt_copies P.ret out_patt ret_type in
  let%bind havoc_oracle = gen_oracle @@ MRet fn in
  let havoc_ret = List.fold_left (fun acc (src,dst) ->
      if havoc_oracle src then
        P.PathSet.add dst acc
      else
        acc
    ) P.PathSet.empty copies in
  return (List.map (fun (s,d) -> (s,RT.RAp d)) copies,havoc_ret)
  
let bind_args ~e_id out_patt call_expr curr_rel body_rel =
  let callee = call_expr.callee in
  let%bind callee_type = get_function_type callee in
  let%bind in_rel = get_in_relation callee in
  let%bind out_rel = get_out_relation callee in
  let args = call_expr.arg_names in
  let%bind (havoc,stable,in_bindings,out_bindings,pre_bindings) = fold_left2i (fun i acc arg_name arg_ty ->
      let%bind acc = acc in
      bind_arg ~fn:callee ~e_id acc (P.var arg_name) (P.arg i) arg_ty
    ) (return (P.PathSet.empty,P.PathSet.empty,[],[],[])) args callee_type.arg_types
  in
  let%bind (return_bindings,havoc_bind) = bind_return ~fn:callee out_patt callee_type.ret_type in
  let%bind havoc_state = get_havoc_state in
  let havoc_state = P.PathSet.union havoc_bind @@ P.PathSet.union (P.PathSet.diff havoc_state stable) havoc in

  let havoc_subst =
    P.PathSet.elements havoc_state |> List.mapi (fun i p ->
        (p,RT.RAp (havoc_ap i p))
      )
  in
  begin%m
      add_relation_flow ~out_ctxt:call_expr.label in_bindings curr_rel in_rel;
       add_implication [
         PRelation (curr_rel,pre_bindings,None);
         PRelation (out_rel,return_bindings @ out_bindings,Some call_expr.label)
       ] @@ PRelation (body_rel,havoc_subst,None);
       set_havoc_state havoc_state
  end

let process_intrinsic out_patt call_expr intr_type curr_rel body_rel =
  (* check pre-conditions *)
  (* TODO: factor this out *)
  let arg_names = fold_lefti (fun i acc arg ->
      StringMap.add (P.arg_name i) arg acc
    ) StringMap.empty call_expr.arg_names
  in
  let type_fail () = failwith @@ "Cannot handle non-integer typed args in built in functions: " ^ call_expr.callee in
  let%bind () =
    miteri (fun i t ->
      let nu_arg = P.var (List.nth call_expr.arg_names i) in
      match t with
      | RT.Int r ->
        lift_refinement ~map:(P.map_root (fun n -> SM.find n arg_names)) ~nu_arg r
        |> miter @@ add_implication [ PRelation (curr_rel,[],None) ]
      | _ -> type_fail ()
    ) intr_type.RT.arg_types
  in
  match out_patt with
  | PNone -> return ()
  | PVar v -> 
    let pre =
      match intr_type.RT.result_type with
      | Int r -> lift_refinement ~map:(P.map_root (fun n -> SM.find n arg_names)) ~nu_arg:(P.var v) r
      | _ -> type_fail ()
    in
    apply_identity_flow ~pre curr_rel body_rel
  | PTuple _ -> type_fail ()


let process_call ~e_id out_patt call_expr curr_rel body_rel =
  let%bind st = copy_state in
  if StringMap.mem call_expr.callee st.bif_types then
    process_intrinsic out_patt call_expr (StringMap.find call_expr.callee st.bif_types) curr_rel body_rel
  else
    bind_args ~e_id out_patt call_expr curr_rel body_rel

let add_indexing_assertion arr_ap ind_ap relation =
  let array_len = P.len arr_ap in
  let%bind () = add_implication [ PRelation(relation,[],None) ] @@ NamedRel ("valid-ind",[RT.RAp ind_ap; RT.RAp array_len ]) in
  add_implication [ PRelation(relation,[],None) ] @@ rel (mk_relation (RT.RAp array_len) ">" (RT.RConst 0))

let apply_patt ~e_id tyenv patt rhs =
  match patt,rhs with
  | _,Call c -> process_call ~e_id patt c
  | PNone,_ -> apply_identity_flow ?pre:None
  | _,Var s ->
    let path = P.var s in
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) @@ compute_patt_copies path patt @@ path_simple_type tyenv path
  | PVar s,Const n -> add_relation_flow [ Const (P.var s,n) ]
  | PVar s,Mkref RNone ->
    add_relation_flow [ Havoc (vderef s) ]
  | PVar s,Mkref (RInt n)  ->
    add_relation_flow [ Const (vderef s,n) ]
  | PVar s,Mkref (RVar v) ->
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) @@ compute_copies (P.var v) (vderef s) @@ path_simple_type tyenv (P.var v)

  | _,Deref v ->
    let copies = compute_patt_copies (vderef v) patt @@ path_simple_type tyenv (vderef v) in
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) copies

  | PVar t,Tuple tl ->
    let tup_root = P.var t in
    let flows,copies = fold_lefti (fun i (flows,copies) r ->
        let tgt_ap = P.t_ind tup_root i in
        match r with
        | RNone -> (Havoc tgt_ap)::flows,copies
        | RInt n -> Const (tgt_ap,n)::flows,copies
        | RVar v ->
          let src_type = path_simple_type tyenv @@ P.var v in
          flows,(compute_copies (P.var v) tgt_ap src_type) @ copies
      ) ([],[]) tl
    in
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) ~flows copies

  | PTuple _,Tuple _ -> assert false
  | PTuple _,_ -> assert false
  | PVar v,Nondet None -> add_relation_flow [ Havoc (P.var v) ]
  | PVar v,Nondet (Some r) ->
    let refinement = lift_refinement ~nu_arg:(P.var v) r in
    apply_identity_flow ~pre:refinement
    
  (* not yet implemented *)
  | PVar v,MkArray len_var ->
    (fun in_rel out_rel ->
      let%bind () = add_assert (RT.RAp (P.var len_var)) ">=" (RT.RConst 0) in_rel in
      let array_root = (P.var v) in
      let l = P.var len_var in
      let ind = P.ind array_root in
      let elem = P.elem array_root in
      let valid_sym_ind = [
        NamedRel ("valid-ind", [RT.RAp ind; RT.RAp l ])
      ] in
      add_relation_flow ~pre:valid_sym_ind [ Const (elem, 0); Copy (l,P.len array_root) ] in_rel out_rel)
  | PVar v,LengthOf arr ->
    add_relation_flow ?pre:None [ Copy (P.len (P.var arr), P.var v) ]
  | PVar v,Read (arr,ind) ->
    (fun in_rel out_rel ->
      let arr_ap = P.var arr in
      let ind_ap = P.var ind in
      
      let array_ind = P.ind arr_ap in
      let elem_ap = P.elem arr_ap in
      let%bind () = add_indexing_assertion arr_ap ind_ap in_rel in
      let copy_pre_cond = PRelation (in_rel,[
            (array_ind, RT.RAp ind_ap);
            (elem_ap, RT.RAp (P.var v))
          ], None) in
      let identity_cond = PRelation (in_rel, [], None) in
      add_implication [ copy_pre_cond; identity_cond ] @@ PRelation (out_rel,[],None))
  | _,Null -> assert false

let relation_name ((e_id,_),expr) ctxt =
  let prefix = Printf.sprintf "%s-%d-" (Option.value ~default:"main_fn" ctxt.curr_fun) e_id in
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
  let bound_paths = List.map (fun (p,_) -> p) args |> P.PathSet.of_list in
  let new_args = curr_args @ (List.rev args) in
  let name = relation_name k ctxt in
  let relation = (name, new_args) in
  { ctxt with relations = relation::ctxt.relations },(relation,tyenv',bound_paths)

let rec process_expr ((relation,tyenv) as st) continuation ((e_id,_),e) =
  let scoped_havoc f ctxt =
    let havoc_set = ctxt.havoc_set in
    let ctxt,r = f ctxt in
    { ctxt with havoc_set },r
  in
  let post_bind paths f ctxt =
    let ctxt,r = f ctxt in
    { ctxt with havoc_set = P.PathSet.diff ctxt.havoc_set paths },r
  in
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
        let copies = compute_copies (P.var v) ret_var @@ path_simple_type tyenv (P.var v) in
        apply_copies ~havoc:false ~sl:(SRet e_id) copies relation out_relation
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
    let copies = compute_copies (P.var rhs) (vderef lhs) @@ List.assoc rhs tyenv in
    apply_copies ~havoc:true ~sl:(SBind e_id) copies relation k_rel >>
    process_expr (k_rel,tyenv) continuation k
      
  | Update (arr,ind,rhs,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    let array_ap = P.var arr in
    let ind_ap = P.var ind in
    let rhs_ap = P.var rhs in

    let sym_ind = P.ind array_ap in
    let sym_elem = P.elem array_ap in
    begin%m
        add_indexing_assertion array_ap ind_ap relation;

         add_implication [
           PRelation (relation,[],None)
         ] @@ PRelation (k_rel,[ (sym_elem, RT.RAp rhs_ap); (sym_ind, RT.RAp ind_ap) ], None);
         add_implication [
           PRelation (relation,[],None);
           rel @@ mk_relation (RT.RAp sym_ind) "!=" (RT.RAp ind_ap)
         ] @@ PRelation (k_rel,[], None);
         process_expr (k_rel,tyenv) continuation k
    end
  | Cond (v,e1,e2) ->
    let%bind e1_rel = fresh_relation_for relation e1 in
    let%bind e2_rel = fresh_relation_for relation e2 in
    
    let mk_pre rel_cond = Relation RT.({
        rel_op1 = RAp (P.var v); rel_cond; rel_op2 = RConst 0 
        })
    in
    begin%m
        apply_identity_flow ~pre:[ mk_pre "=" ] relation e1_rel;
         scoped_havoc @@ process_expr (e1_rel,tyenv) continuation e1;
         apply_identity_flow ~pre:[ mk_pre "!=" ] relation e2_rel;
         process_expr (e2_rel,tyenv) continuation e2
    end
  | NCond _ -> assert false
    
  | Let (patt,rhs,k) ->
    let%bind k_rel,tyenv',bound_set = fresh_bind_relation e_id st patt k in
    apply_patt ~e_id tyenv patt rhs relation k_rel >>
    post_bind bound_set @@ process_expr (k_rel,tyenv') continuation k
      
  | EAnnot _ -> assert false
    
  | Assert (assrt, k) ->
    let%bind k_rel = fresh_relation_for relation k in
    add_assert_cond assrt relation >>
    apply_identity_flow relation k_rel >>
    process_expr (k_rel,tyenv) continuation k
      
  | Alias (lhs,s_ap,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    let rhs_ap = match s_ap with
      | AVar v -> P.var v
      | AProj (v,i) -> P.t_ind (P.var v) i
      | ADeref v -> P.deref @@ P.var v
      | APtrProj (v,i) -> P.t_ind (P.deref @@ P.var v) i
    in
    let lhs_type = List.assoc lhs tyenv in
    let rhs_subst = compute_copies (P.var lhs) rhs_ap lhs_type in
    let%bind havoc_oracle = gen_for_alias e_id in
    let lhs_output = type_to_paths (P.var lhs) lhs_type |>
        List.mapi (fun i p ->
          if (havoc_oracle p) then
            Some (p,RT.RAp (havoc_ap i p))
          else
            None
        ) |> List.filter_map Fun.id
    in
    let out_subst = fold_lefti (fun i acc (src,out) ->
        if (havoc_oracle out) then
          (out,RT.RAp (havoc_ap i src))::acc
        else
          (copy_to_flow (src,out))::acc
      ) lhs_output rhs_subst in
    add_implication [ PRelation (relation,(List.map copy_to_flow rhs_subst),None) ] @@ PRelation (k_rel,out_subst,None) >>
    process_expr (k_rel,tyenv) continuation k

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
                        
  let havoc_set = fold_left2i (fun i acc nm ty ->
      List.fold_left (fun acc path ->
        let arg_id = P.map_root (fun _ -> P.arg_name i) path in
        if havoc_oracle ctxt (OI.MArg fn.name) arg_id then 
          P.PathSet.add path acc
        else
          acc
      ) acc @@ type_to_paths (P.var nm) ty
    ) P.PathSet.empty fn.args fn_type.arg_types in
  let mapped_in_args = map_args in_args in
  let mapped_out_args = map_args out_args in
  let cont = (Some (out_nm, mapped_out_args)),Some P.ret in
  let ctxt,() = process_expr ((in_nm,mapped_in_args),initial_env) cont fn.body {ctxt with curr_fun = Some fn.name; havoc_set } in
  ctxt

let analyze_main start_rel main ctxt =
  let ctxt,() = process_expr (start_rel,[]) (None,None) main ctxt in
  ctxt

let infer ~bif_types (simple_theta,side_results) o_hints (fns,main) =
  let (fenv,relations) = StringMap.fold (fun name ty (theta,rel) ->
      let arg_paths =
        List.mapi (fun i arg_t ->
          type_to_paths ~pre:true (P.arg i) arg_t
        ) ty.arg_types
      in
      let in_rel_types = List.map (fun p -> (p,ZInt)) @@ List.concat arg_paths in
      let ret_rel = type_to_paths P.ret ty.ret_type |> List.map (fun p -> (p,ZInt)) in
      let out_rel_types = in_rel_types @ ret_rel in
      let in_rel = (name ^ "-in", in_rel_types) in
      let out_rel = (name ^ "-out", out_rel_types) in
      let ftype = (in_rel,out_rel,ty) in
      (StringMap.add name ftype theta,in_rel::out_rel::rel)
    ) simple_theta (StringMap.empty, []) in
  let start_name = "program_start" in
  let entry_relation = (start_name, []) in
  let relations = entry_relation::relations in
  let empty_ctxt = {
    relations;
    o_hints;
    curr_fun = None;
    let_types = side_results.SimpleChecker.SideAnalysis.let_types;
    bif_types;
    fenv;
    impl = [];
    havoc_set = P.PathSet.empty
  } in
  let ctxt = List.fold_left (fun ctxt fn ->
      analyze_function fn ctxt
    ) empty_ctxt fns in
  let ctxt = analyze_main entry_relation main { ctxt with curr_fun = None } in
  (* let _ = List.iter print_relation ctxt.relations in *)
  (ctxt.relations,ctxt.impl,start_name)


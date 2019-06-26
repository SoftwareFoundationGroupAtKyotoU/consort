open Ast
open RefinementTypes
open Sexplib.Std
    
module SM = StringMap

let loc_to_string =
  let labeled_expr s i = Printf.sprintf "%s@%d" s i in
  let fn_loc fn l = Printf.sprintf "fn %s %s" fn l in
  function
  | LCond i -> labeled_expr "if" i
  | LArg f -> fn_loc f "Arg"
  | LReturn f -> fn_loc f "Ret"
  | LOutput f -> fn_loc f "Out"
  | LAlias i -> labeled_expr "alias" i
  | LLet i -> labeled_expr "let" i
  | LCall i -> labeled_expr "call" i


type pred_context = {
  fv: string list;
  loc: pred_loc;
  target_var: string option
}

type location = {
  host_function: string;
  term: Ast.exp
}

type funenv = funtype SM.t
type tenv = typ SM.t

type oante = ownership * [ `Ge | `Gt | `Eq ] * float [@@deriving sexp]

let tenv_of_sexp = SM.t_of_sexp ~v:typ_of_sexp

let sexp_of_tenv = SM.sexp_of_t ~v:sexp_of_typ

type tcon = {
  env: tenv;
  ante: refinement;
  conseq: refinement;
  owner_ante: oante list;
}[@@deriving sexp]

type ocon =
  (* Constraint ownership variable n to be 1 *)
  | Write of ownership
  (* ownership has to be greater than 0 *)
  | Live of ownership
  (* ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Shuff of (ownership * ownership) * (ownership * ownership)
  | Split of ownership * (ownership * ownership)
  | Eq of ownership * ownership

module IntMap = Map.Make(struct
    type t = int
    let compare n1 n2 = n1 - n2
  end)

type context = {
  theta: funenv;
  gamma: tenv;
  ownership: ocon list;
  ovars: int list;
  refinements: tcon list;
  pred_arity: int IntMap.t;
  v_counter: int;
  pred_detail: (int,pred_context) Hashtbl.t;
}

module Result = struct
  type t = {
    theta: funenv;
    ownership: ocon list;
    ovars: int list;
    refinements: tcon list;
    arity: int IntMap.t
  }
end

let alloc_ovar ctxt =
  ({ ctxt with v_counter = ctxt.v_counter + 1; ovars = ctxt.v_counter::ctxt.ovars }, OVar ctxt.v_counter)

let (>>) f g = fun st ->
  let (st',v1) = f st in
  let (st'', v2) = g st' in
  (st'',(v1, v2))

let add_owner_con l ctxt = { ctxt with ownership = l @ ctxt.ownership  }

let update_map v t m =
  SM.remove v m
  |> SM.add v t

let update_type v t ctxt =
  { ctxt with gamma = update_map v t ctxt.gamma }

let add_type v t ctxt =
  let te =
    SM.add v t ctxt.gamma
  in
  { ctxt with gamma = te }

let split_ref_type ctxt (t,o) =
  let (ctxt,(o1,o2)) = (alloc_ovar >> alloc_ovar) ctxt in
  let t1 = `Ref (t,o1) in
  let t2 = `Ref (t,o2) in
  (add_owner_con [Split (o,(o1, o2))] ctxt, (t1, t2))

let split_type ctxt t =
  match t with
  | `Int _ -> (ctxt, (t,t))
  | `Ref (t,o) ->
    split_ref_type ctxt (t,o)

let with_type t ctxt = (ctxt, t)

let deref r = r

let add_constraint gamma ctxt ?(o=[]) ante conseq =
  { ctxt with
    refinements = {
      env = gamma;
      ante;
      conseq;
      owner_ante = o;
    }::ctxt.refinements
  }

let constrain_owner t1 t2 ctxt =
  match t1,t2 with
  | `Ref (_,o1),`Ref (_,o2) ->
    add_owner_con [Eq (o1,o2)] ctxt
  | _ -> ctxt

let constrain_type gamma t r ctxt =
  add_constraint gamma ctxt (get_refinement t) r

let constrain_var gamma ctxt var r =
  constrain_type gamma (SM.find var gamma) r ctxt

let alloc_pred ?target_var ~loc fv ctxt =
  let n = ctxt.v_counter in
  let arity = (List.length fv) -
      (match target_var with
      | Some v when List.mem v fv -> 1
      | _ -> 0) + 1 + !KCFA.cfa (* 1 for nu and k for context *)
  in
  Hashtbl.add ctxt.pred_detail n { fv; loc; target_var };
  ({ ctxt with
     v_counter = n + 1;
     pred_arity = IntMap.add n arity ctxt.pred_arity
   }, n)

let make_fresh_pred ?target_var ~loc ~fv ctxt =
  let (ctxt',p) = alloc_pred ?target_var ~loc fv ctxt in
  (ctxt',Pred (p,fv,target_var))

let update_var_refinement var r ctxt =
  let new_type =
    SM.find var ctxt.gamma |> update_refinement r
  in
  update_type var new_type ctxt

let subtype_fresh ~loc gamma ctxt v ~fv =
  let (ctxt',fresh_pred) = make_fresh_pred ~target_var:v ~loc ~fv ctxt in
  constrain_var gamma ctxt' v fresh_pred
  |> update_var_refinement v fresh_pred

let rec free_vars_contains v r =
  let imm_is_var i = match i with IInt _ -> false | IVar v' -> v = v' in
  match r with
  | Pred (_,l,_)
  | NamedPred (_,l,_)
  | CtxtPred (_,_,l,_) -> List.mem v l
  | Relation { rel_op1 = op1; rel_op2 = op2; _ } ->
    imm_is_var op2 || (match op1 with
      RImm v -> imm_is_var v | Nu -> false)
  | And (r1, r2) -> free_vars_contains v r1 || free_vars_contains v r2       
  | _ -> false

let predicate_vars kv =
  List.fold_left (fun acc (k, t) ->
      match t with
      | `Int _ -> k::acc
      | _ -> acc
  ) [] kv |> List.rev

let gamma_predicate_vars gamma =
  SM.bindings gamma |> predicate_vars

let remove_var ~loc v t ctxt =
  let curr_te = ctxt.gamma in
  let ctxt = { ctxt with gamma = SM.remove v ctxt.gamma } in
  let bindings = SM.bindings ctxt.gamma in
  let in_scope = predicate_vars bindings in
  let need_update = List.filter (fun (_,t) ->
      get_refinement t |> free_vars_contains v
    ) bindings in
  let ctxt' = List.fold_left (fun ctxt' (k,_) ->
    subtype_fresh ~loc curr_te ctxt' k ~fv:in_scope
    ) ctxt need_update in
  if get_refinement t |> free_vars_contains v then
    let (ctxt'',r') = make_fresh_pred ~loc ~fv:in_scope ctxt' in
    (constrain_type curr_te t r' ctxt'', update_refinement r' t)
  else
    (ctxt', t)

let unsafe_get o =
  match o with
  | Some l -> l
  | None -> failwith "That's why it's called unsafe"

let imm_to_lin = function
  | IVar v -> LVar (1,v)
  | IInt i -> LConst i

let lift_relation { rop1; cond; rop2 } =
  Relation { rel_op1 = RImm rop1; rel_cond = cond; rel_op2 = rop2 }

let add_relation_constr t r =
  let r' = And (get_refinement t,r) in
  update_refinement r' t

let dump_env ?(msg) tev =
  (match msg with
  | Some m -> print_endline m;
  | None -> ());
  sexp_of_tenv tev |> Sexplib.Sexp.to_string_hum |> print_endline

let post_update_type t = match t with
  | `Int _ -> false
  | `Ref _ -> true

(* eq_type must be the type of target *)
let strengthen_eq ~strengthen_type ~eq_type ~target =
  match eq_type with
  | `Int _ ->
    add_relation_constr strengthen_type @@ Relation {
        rel_op1 = Nu; rel_cond = "="; rel_op2 = IVar target
      }
  | `Ref _ -> strengthen_type

let decompose_ref r =
  (unsafe_get_ownership r,get_refinement r)

let apply_matrix ((o1,r1),(o2,r2)) (out_o,out_r) ctxt =
  let mk_constraint oante ante =
    {
      env = ctxt.gamma;
      ante = ante;
      conseq = out_r;
      owner_ante = (out_o,`Gt,0.0)::oante;
    }
  in
  let cons_s = [
    mk_constraint [(o1,`Gt,0.0);(o2,`Gt,0.0)] @@ And (r1,r2);
    mk_constraint [(o1,`Gt,0.0);(o2,`Eq,0.0)] r1;
    mk_constraint [(o2,`Gt,0.0);(o1,`Eq,0.0)] r2;
  ] in
  { ctxt with refinements = cons_s @ ctxt.refinements }
let rec process_expr ctxt e =
  let lkp v = SM.find v ctxt.gamma in
  let lkp_ref v = match lkp v with
    | `Ref (r,o) -> (r,o)
    | _ -> failwith "Not actually a ref"
  in
  match e with
  | EVar v ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp v in
    (update_type v t1 ctxt', t2)
  | Seq (e1, e2) ->
    let (ctxt', _) = process_expr ctxt e1 in
    process_expr ctxt' e2
  | Assign (lhs,_,IVar rhs,cont) ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp rhs in
    let (_,o)  = lkp_ref lhs in
    let nxt = add_owner_con [Write o] ctxt'
    |> update_type rhs t1
    |> update_type lhs @@ strengthen_eq ~target:rhs ~eq_type:t2 ~strengthen_type:(ref_of t2 o) in
    process_expr nxt cont
  | Assign (lhs,_,IInt i,cont) ->
    let (_,o) = lkp_ref lhs in
    let ctxt' =
      add_owner_con [Write o] ctxt
      |> update_type lhs @@ ref_of (`Int (ConstEq i)) o
    in
    process_expr ctxt' cont
  | Let (i,v,lhs,exp) ->
    let bound_ctxt = begin
    match lhs with
    | Var left_v ->
      let (ctxt',(t1,t2)) = split_type ctxt @@ lkp left_v in
      ctxt'
      |> update_type left_v @@ strengthen_eq ~strengthen_type:t1 ~eq_type:t2 ~target:v
      |> add_type v @@ strengthen_eq ~strengthen_type:t2 ~eq_type:t1 ~target:left_v
    | Const n -> add_type v (`Int (ConstEq n)) ctxt
    | Nondet ->
      add_type v (`Int Top) ctxt
    | Call c ->
      let (ctxt,ret) = process_call ctxt c in
      add_type v ret ctxt
    | Field (ptr,_) ->
      let (r,o) = lkp_ref ptr in
      let target_type = (deref r :> typ) in
      let (ctxt',(t1,t2)) = split_type ctxt target_type in
      ctxt'
      |> update_type ptr @@ strengthen_eq ~strengthen_type:(ref_of t1 o) ~eq_type:t1 ~target:v
      |> add_type v t2
      |> add_owner_con [Live o]
    | Mkref init' ->
      let init = List.hd init' |> snd in
      match init with
      | RNone -> add_type v (`Ref (`Int Top,OConst 1.0)) ctxt
      | RInt n -> add_type v (`Ref (`Int (ConstEq n),OConst 1.0)) ctxt
      | RVar r_var ->
        let (ctxt',(t1,t2)) = split_type ctxt @@ lkp r_var in
        let t2' =
          strengthen_eq ~strengthen_type:(ref_of t2 @@ OConst 1.0) ~eq_type:t2 ~target:r_var
        in
        update_type r_var t1 ctxt'
        |> add_type v t2'
    end in
    let (ctxt',ret_t) = process_expr bound_ctxt exp in
    let (ctxt'',ret_t') = remove_var ~loc:(LLet i) v ret_t ctxt' in
    (ctxt'', ret_t')
  | Assert (relation,cont) ->
    cont
    |> process_expr @@ add_constraint ctxt.gamma ctxt Top (lift_relation relation)
  | Alias (id,v1,v2,cont) ->
    let loc = LAlias id in
    let (r1,o1) = lkp_ref v1 in
    let (r2,o2) = lkp_ref v2 in
    let free_vars = predicate_vars @@ SM.bindings ctxt.gamma in
    let (ctxtf1,t1',p1') = make_fresh_type ~target_var:v1 ~loc ~fv:free_vars (lkp v1) ctxt in
    let (ctxt'',t2',p2') = make_fresh_type ~target_var:v2 ~loc ~fv:free_vars (lkp v2) ctxtf1 in
    let o1' = unsafe_get_ownership t1' in
    let o2' = unsafe_get_ownership t2' in
    let constraint_matrix = apply_matrix ((o1,get_refinement (r1 :> typ)),(o2,get_refinement (r2:> typ))) in
    let ctxt_constrained =
      ctxt''
      |> constraint_matrix (o1',p1')
      |> constraint_matrix (o2',p2')
    in
    let own = Shuff ((o1,o2),(o1',o2')) in
    let res = { ctxt_constrained with
                ownership = own::ctxt_constrained.ownership
              }
      |> update_type v1 @@ t1'
      |> update_type v2 @@ t2'
    in
    process_expr res cont
  | Cond(i,v,e1,e2) ->
    let add_pc_refinement ctxt cond =
      let curr_ref = lkp v in
      let branch_refinement = {
        rel_op1 = Nu;
        rel_cond = cond;
        rel_op2 = IInt 0
      } in
      ctxt |>
      update_type v @@ add_relation_constr curr_ref @@ Relation branch_refinement 
    in
    let (ctxt1,t1) = process_expr (add_pc_refinement ctxt "=") e1 in
    let (ctxt2,t2) = process_expr (add_pc_refinement {
        ctxt with
          refinements = ctxt1.refinements;
          v_counter = ctxt1.v_counter;
          ownership = ctxt1.ownership;
          pred_arity = ctxt1.pred_arity;
          ovars = ctxt1.ovars
        } "!=") e2 in
    let loc = LCond i in
    let u_ctxt = { ctxt2 with gamma = SM.empty } in
    let b1 = SM.bindings ctxt1.gamma in
    let b2 = SM.bindings ctxt2.gamma in
    let predicate_vars = predicate_vars @@ b1 in
    let subsume_types ctxt ?target_var t1 t2 =
      let (ctxt',t,r') = make_fresh_type ~loc ?target_var ~fv:predicate_vars t1 ctxt in
      let c_up =
        constrain_type ctxt1.gamma t1 r' ctxt'
        |> constrain_type ctxt2.gamma t2 r'
        |> constrain_owner t1 t
        |> constrain_owner t2 t
      in
      (c_up,t)
    in
    let c_sub = List.fold_left2 (fun ctxt (k1,t1) (k2,t2) ->
        assert (k1 = k2);
        let (ctxt',t) = subsume_types ctxt ~target_var:k1 t1 t2 in
        add_type k1 t ctxt'
      ) u_ctxt b1 b2 in
    subsume_types c_sub t1 t2
and make_fresh_reftype ?target_var ~loc ~fv t ctxt =
  match t with
  | `Int _ ->
    let (ctxt',r) = make_fresh_pred ?target_var ~loc ~fv ctxt in 
    (ctxt',`Int r,r)
and make_fresh_type ?target_var ~loc ~fv t ctxt =
  match t with
  | `Int _ as t'-> (make_fresh_reftype ?target_var ~loc ~fv t' ctxt :> (context * typ * refinement))
  | `Ref (r,_) -> 
    let (ctxt',o') = alloc_ovar ctxt in
    let (ctxt'',r',p) = make_fresh_reftype ?target_var ~loc ~fv r ctxt' in
    (ctxt'',`Ref (r',o'),p)
and process_call ctxt c =
  let arg_bindings = List.map (fun k ->
      (k,SM.find k ctxt.gamma)) c.arg_names
  in
  let p_vars = predicate_vars arg_bindings in
  let inst ?target_var f_refinement =
    match f_refinement with
    | InfPred p -> 
      CtxtPred (c.label,p,p_vars,target_var)
    | True -> Top
    | BuiltInPred f -> NamedPred (f,p_vars,target_var)
  in
  let subst_type ?target_var t =
    update_refinement (inst ?target_var @@ get_refinement t) t
  in
  let input_env = ctxt.gamma in
  let callee_type = SM.find c.callee ctxt.theta in
  let in_out_types = List.combine callee_type.arg_types callee_type.output_types in
  let post_type_vars = gamma_predicate_vars ctxt.gamma in
  let updated_ctxt = List.fold_left2 (fun acc (k,arg_t) (in_t,out_t) ->
      let constrain_in c t =
        constrain_var input_env c k (inst ~target_var:k @@ get_refinement in_t)
        |> constrain_owner t in_t
      in
      if (post_update_type arg_t) then
        (* split the argument type *)
        let (ctxt',(formal,resid)) = split_type acc arg_t in
        (* the (substituted) argument type *)
        let output_type = subst_type ~target_var:k out_t in
        let (ctxt'',fresh,p') =
          (* constrain one "half" to be a subtype of the formal *)
          constrain_in ctxt' formal
          (* then generate a new fresh type to describe the output type *)
          |> make_fresh_type ~target_var:k ~loc:(LCall c.label) ~fv:post_type_vars output_type
        in
        let o' = unsafe_get_ownership fresh in
        (* constrain the components o' p' of fresh such that fresh = output_type + resid *)
        apply_matrix
          (decompose_ref resid, decompose_ref output_type)
          (o',p') ctxt''
        |> add_owner_con [ Split (o',(unsafe_get_ownership output_type, unsafe_get_ownership resid)) ]
        |> update_type k fresh
      else
        constrain_in acc arg_t
    ) ctxt arg_bindings in_out_types
  in
  let result = subst_type callee_type.result_type in
  (updated_ctxt, result)

let process_function_bind ctxt fdef =
  let arg_names = fdef.args in
  let f_typ = SM.find fdef.name ctxt.theta in
  let typ_template = List.combine arg_names f_typ.arg_types in
  let fv = predicate_vars typ_template in
  let subst_refinement ?target t =
      let pred_var = match get_refinement t with
        | InfPred i -> i
        | _ -> assert false
      in
      Pred (pred_var,fv,target)
  in
  let init_env = List.map (fun (n,t) ->
      let t' = update_refinement (subst_refinement ~target:n t) t in
      (n,t')
    ) typ_template |>
      List.fold_left (fun acc (v,ty) ->
        SM.add v ty acc
      ) SM.empty
  in
  let (ctxt',t') = process_expr { ctxt with gamma = init_env } fdef.body in
  let out_typ_template = List.combine arg_names f_typ.output_types in
  let ctxt'' = List.fold_left (fun acc (v,out_ty) ->
      let out_pred = subst_refinement ~target:v out_ty in
      constrain_var acc.gamma acc v out_pred
      |> constrain_owner out_ty (SM.find v acc.gamma)
    ) ctxt' out_typ_template in
  let return_pred = subst_refinement f_typ.result_type in
  constrain_type ctxt''.gamma t' return_pred ctxt''

let process_function ctxt fdef =
  let c = process_function_bind ctxt fdef in
  { c with gamma = SM.empty }

let print_pred_details t =
  Hashtbl.iter (fun k { fv; loc; target_var } ->
    Printf.fprintf stderr "%d: >>\n" k;
    Printf.fprintf stderr "  Free vars: [%s]\n" @@ String.concat ", " fv;
    Printf.fprintf stderr "  Target var: %s\n" @@ (match target_var with
    | Some v -> v
    | None -> "<NONE>");
    Printf.fprintf stderr "  At: %s\n<<\n" @@ loc_to_string loc
  ) t
  
let infer ~print_pred ~intrinsics st (fns,main) =
  let init_fun_type ctxt f_def =
    let gen_refine_templ ?target_var ~loc free_vars t ctxt =
      match t with
      | `Int ->
        let (ctxt',p) = alloc_pred ?target_var ~loc free_vars ctxt in
        (ctxt',(`Int (InfPred p)))
      | `IntRef ->
        let (ctxt',(p,o)) = ((alloc_pred ?target_var ~loc free_vars) >> alloc_ovar) ctxt in
        (ctxt',`Ref (`Int (InfPred p),o))
    in
    let gen_arg_preds ~loc fv arg_templ ctxt = List.fold_right (fun (k,t) (acc_c,acc_ty) ->
        let (ctxt',t') = gen_refine_templ ~target_var:k ~loc fv t acc_c in
        (ctxt',t'::acc_ty)
      ) arg_templ (ctxt,[])
    in
    let simple_ftype = SM.find f_def.name st in
    let arg_templ = List.combine f_def.args simple_ftype.SimpleTypes.arg_types in
    let free_vars = List.filter (fun (_,t) -> t = `Int) arg_templ |> List.map fst in
    let (ctxt',arg_types) = gen_arg_preds ~loc:(LArg f_def.name) free_vars arg_templ ctxt in
    let (ctxt'',output_types) = gen_arg_preds ~loc:(LOutput f_def.name) free_vars arg_templ ctxt' in
    let (ctxt''', result_type) =
      gen_refine_templ ~loc:(LReturn f_def.name) free_vars simple_ftype.SimpleTypes.ret_type ctxt''
    in
    { ctxt''' with
      theta = SM.add f_def.name {
          arg_types; output_types; result_type
        } ctxt'''.theta
    }
  in
  let initial_ctxt = {
    theta = intrinsics;
    gamma = SM.empty;
    ownership = [];
    ovars = [];
    refinements = [];
    pred_arity = IntMap.empty;
    v_counter = 0;
    pred_detail = Hashtbl.create 10;
  } in
  let ctxt = List.fold_left init_fun_type initial_ctxt fns in
  let ctxt' = List.fold_left process_function ctxt fns in
  let ({ pred_detail; refinements; ownership; ovars; pred_arity; theta; _ },_) = process_expr ctxt' main in
  if print_pred then print_pred_details pred_detail;
  Result.{
    ownership;
    ovars;
    refinements;
    theta;
    arity = pred_arity
  }
  

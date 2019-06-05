open Ast
open Sexplib.Std
    
module SM = SimpleChecker.StringMap

type pred_loc =
  | LCond of int
  | LArg of string
  | LReturn of string
  | LOutput of string
  | LAlias of int
  | LLet of int

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


type pred_context = {
  fv: string list;
  loc: pred_loc;
  target_var: string option
}

type rel_op =
    Nu
  | RImm of imm_op [@@deriving sexp]

type lin_op =
  | LConst of int
  | LVar of (int * string) [@@deriving sexp]

(* For the moment, a linear equation is just addition between two variables *)
type lin_eq = {
  op1: lin_op;
  op2: lin_op
}[@@deriving sexp]

type refinement_rel = {
  rel_op1: rel_op;
  rel_cond: cond;
  rel_op2: imm_op;
} [@@deriving sexp]

(* 
Pred n,l: A predicate symbol with name n over variables l (nu is implicit)
CtxtPred c,n,l: A Preciate symbol with name n over variables l with explicit context c
Top: unconstrained
Const: the constaint constraint
Eq: equality with variable b
Linear: a linear equation over variables
*)
type refinement =
  | Pred of int * string list * string option
  | CtxtPred of int * int * string list * string option
  | Top
  | ConstEq of int
  (*  | Eq of string*)
  | Linear of lin_eq
  | Relation of refinement_rel
  | And of refinement * refinement [@@deriving sexp]

type ownership =
    OVar of int
  | OConst of float[@@deriving sexp]

type 'a ref_contents = [ `Int of 'a ] [@@deriving sexp]

type 'a _typ = [
  | `Int of 'a
  | `Ref of 'a ref_contents * ownership
][@@deriving sexp]

type typ = refinement _typ [@@deriving sexp]
type ftyp = int  _typ

type etype = [
  | `UnitT
  | typ
]

type funtype = {
  arg_types: ftyp list;
  output_types: ftyp list;
  result_type: ftyp option
}

type location = {
  host_function: string;
  term: Ast.exp
}

type funenv = funtype SM.t
type tenv = typ SM.t

type oante = ownership * [ `Ge | `Gt | `Eq ] * float [@@deriving sexp]

let tenv_of_sexp s =
  [%of_sexp: (string * typ) list] s
  |> List.fold_left (fun acc (k,v) ->
      SM.add k v acc) SM.empty

let sexp_of_tenv t =
  SM.bindings t
  |> [%sexp_of: (string * typ) list]

type tcon = {
  env: tenv;
  ante: refinement;
  conseq: refinement;
  owner_ante: oante list;
  pc: (string * string) list
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
  path_condition: (string * string) list
}

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

let ref_of t1 o =
  match t1 with
  | `UnitT | `Ref _ -> failwith "Can't have reference to t"
  | `Int _ as t -> `Ref (t,o)

let deref r = r

let add_constraint pc gamma ctxt ?(o=[]) ante conseq =
  { ctxt with
    refinements = {
      env = gamma;
      ante;
      conseq;
      owner_ante = o;
      pc
    }::ctxt.refinements
  }

let constrain_owner t1 t2 ctxt =
  match t1,t2 with
  | `Ref (_,o1),`Ref (_,o2) ->
    add_owner_con [Eq (o1,o2)] ctxt
  | _ -> ctxt

let update_content_ref r = function
  | `Int _ -> `Int r

let update_refinement r = function
  | `Int _ as t -> (update_content_ref r t :> 'a _typ)
  | `Ref (t,o) -> `Ref (update_content_ref r t,o)

let rec get_refinement : 'a _typ -> 'a = function
    `Int r -> r
  | `Ref (t,_) -> get_refinement (t :'a ref_contents :> 'a _typ)

let unsafe_get_ownership = function
  | `Ref (_,o) -> o
  | _ -> failwith "This is why its unsafe"

let constrain_type pc gamma t r ctxt =
  add_constraint pc gamma ctxt (get_refinement t) r

let constrain_var pc gamma ctxt var r =
  constrain_type pc gamma (SM.find var gamma) r ctxt

let alloc_pred ?target_var ~loc fv ctxt =
  let n = ctxt.v_counter in
  let arity = (List.length fv) -
      (match target_var with
      | Some v when List.mem v fv -> 1
      | _ -> 0) + 2 (* 1 for nu and 1 for context *)
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

let subtype_fresh ~loc pc gamma ctxt v ~fv =
  let (ctxt',fresh_pred) = make_fresh_pred ~target_var:v ~loc ~fv ctxt in
  constrain_var pc gamma ctxt' v fresh_pred
  |> update_var_refinement v fresh_pred

let update_pc (new_pc : (string * string) list) ctxt =
  { ctxt with path_condition = new_pc }

let add_pc (p: string * string) ctxt =
  let l : (string * string) list = ctxt.path_condition in
  update_pc (p::l) ctxt

let rec free_vars_contains v r =
  let imm_is_var i = match i with IInt _ -> false | IVar v' -> v = v' in
  let lop_is_var = function
    | LConst _ -> false
    | LVar (_,v') -> v = v'
  in
  match r with
  | Pred (_,l,_)
  | CtxtPred (_,_,l,_) -> List.mem v l
  | Relation { rel_op1 = op1; rel_op2 = op2; _ } ->
    imm_is_var op2 || (match op1 with
      RImm v -> imm_is_var v | Nu -> false)
  | Linear { op1; op2 } -> (lop_is_var op1) || (lop_is_var op2)
  | And (r1, r2) -> free_vars_contains v r1 || free_vars_contains v r2       
  | _ -> false

let predicate_vars kv =
  List.fold_left (fun acc (k, t) ->
      match t with
      | `Int _ -> k::acc
      | _ -> acc
  ) [] kv |> List.rev

let remove_var pc ~loc v ctxt =
  let curr_te = ctxt.gamma in
  let ctxt = { ctxt with gamma = SM.remove v ctxt.gamma } in
  let bindings = SM.bindings ctxt.gamma in
  let in_scope = predicate_vars bindings in
  let need_update = List.filter (fun (_,t) ->
      get_refinement t |> free_vars_contains v
    ) bindings in
  List.fold_left (fun ctxt' (k,_) ->
    subtype_fresh pc ~loc curr_te ctxt' k ~fv:in_scope
  ) ctxt need_update

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
    
let rec process_expr ctxt e =
  let lkp v = SM.find v ctxt.gamma in
  let lkp_ref v = match lkp v with
    | `Ref (r,o) -> (r,o)
    | _ -> failwith "Not actually a ref"
  in
  match e with
  | Unit -> (ctxt, `UnitT)
  | EInt i -> (ctxt, `Int (ConstEq i))
  | EVar v ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp v in
    (update_type v t1 ctxt', (t2 :> etype))
  | Seq (e1, e2) ->
    let (ctxt', _) = process_expr ctxt e1 in
    process_expr ctxt' e2
  | Assign (lhs,IVar rhs) ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp rhs in
    let (_,o)  = lkp_ref lhs in
    add_owner_con [Write o] ctxt'
    |> update_type rhs t1
    |> update_type lhs (ref_of t2 o)
    |> with_type `UnitT
  | Assign (lhs,IInt i) ->
    let (_,o) = lkp_ref lhs in
    add_owner_con [Write o] ctxt
    |> update_type lhs @@ ref_of (`Int (ConstEq i)) o
    |> with_type `UnitT
  | Let (i,v,lhs,exp) ->
    let bound_ctxt = begin
    match lhs with
    | Var left_v ->
      let (ctxt',(t1,t2)) = split_type ctxt @@ lkp left_v in
      update_type left_v t1 ctxt'
      |> add_pc (v,left_v)
      |> add_type v t2
    | Const n -> add_type v (`Int (ConstEq n)) ctxt
    | Plus (v1,v2) ->
      add_type v (`Int (Linear { op1 = imm_to_lin v1; op2 = imm_to_lin v2 })) ctxt
    | Nondet ->
      add_type v (`Int Top) ctxt
    | Call c ->
      let (ctxt,ret) = process_call ctxt c in
      add_type v (unsafe_get ret) ctxt
    | Deref ptr ->
      let (r,o) = lkp_ref ptr in
      let target_type = (deref r :> typ) in
      let (ctxt',(t1,t2)) = split_type ctxt target_type in
      update_type ptr (add_relation_constr (ref_of t1 o) (Relation {
            rel_op1 = Nu; rel_cond = Eq; rel_op2 = IVar v
          })) ctxt'
      |> add_type v t2
      |> add_owner_con [Live o]
    | Mkref init ->
      match init with
      | RNone -> add_type v (`Ref (`Int Top,OConst 1.0)) ctxt
      | RInt n -> add_type v (`Ref (`Int (ConstEq n),OConst 1.0)) ctxt
      | RVar r_var ->
        let (ctxt',(t1,t2)) = split_type ctxt @@ lkp r_var in
        update_type r_var t1 ctxt'
        |> add_type v (ref_of t2 @@ OConst 1.0)
    end in
    let (ctxt',ret_t) = process_expr bound_ctxt exp in
    remove_var ctxt'.path_condition ~loc:(LLet i) v ctxt'
    |> update_pc ctxt.path_condition
    |> with_type ret_t
  | ECall c -> begin
    let (ctxt, ret) = process_call ctxt c in
    match ret with
    | None -> (ctxt, `UnitT)
    | Some t -> (ctxt, (t :> etype))
    end
  | Assert relation ->
    (add_constraint ctxt.path_condition ctxt.gamma ctxt Top (lift_relation relation), `UnitT)
  | Alias (id,v1,v2) ->
    let loc = LAlias id in
    let (r1,o1) = lkp_ref v1 in
    let (r2,o2) = lkp_ref v2 in
    let free_vars = predicate_vars @@ SM.bindings ctxt.gamma in
    let (ctxtf1,t1',p1') = make_fresh_type ~target_var:v1 ~loc ~fv:free_vars (lkp v1) ctxt in
    let (ctxt'',t2',p2') = make_fresh_type ~target_var:v2 ~loc ~fv:free_vars (lkp v2) ctxtf1 in
    let o1' = unsafe_get_ownership t1' in
    let o2' = unsafe_get_ownership t2' in
    let constraints = [
      {
        env = ctxt''.gamma;
        ante = get_refinement (r1 :> typ);
        conseq = p1';
        owner_ante = [(o1,`Gt,0.0); (o1',`Gt,0.0)];
        pc = ctxt.path_condition
      };
      {
        env = ctxt''.gamma;
        ante = get_refinement (r1 :> typ);
        conseq = p2';
        owner_ante = [(o1,`Gt,0.0);(o2',`Gt,0.0)];
        pc = ctxt.path_condition
      };
      {
        env = ctxt''.gamma;
        ante = get_refinement (r2 :> typ);
        conseq = p1';
        owner_ante = [(o2,`Gt,0.0);(o1',`Gt,0.0)];
        pc = ctxt.path_condition
      };
      {
        env = ctxt''.gamma;
        ante = get_refinement (r2 :> typ);
        conseq = p2';
        owner_ante = [(o2,`Gt,0.0);(o2',`Gt,0.0)];
        pc = ctxt.path_condition
      }
    ] in
    let own = Shuff ((o1,o2),(o1',o2')) in
    let res = { ctxt'' with
                ownership = own::ctxt''.ownership;
                refinements = constraints@ctxt''.refinements
              }
      |> update_type v1 @@ t1'
      |> update_type v2 @@ t2'
    in
    (res, `UnitT)
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
    let (ctxt1,t1) = process_expr (add_pc_refinement ctxt Eq) e1 in
    let (ctxt2,t2) = process_expr (add_pc_refinement {
        ctxt with
          refinements = ctxt1.refinements;
          v_counter = ctxt1.v_counter;
          ownership = ctxt1.ownership;
          pred_arity = ctxt1.pred_arity;
          ovars = ctxt1.ovars
        } Neq) e2 in
    let loc = LCond i in
    let u_ctxt = { ctxt2 with gamma = SM.empty } in
    let b1 = SM.bindings ctxt1.gamma in
    let b2 = SM.bindings ctxt2.gamma in
    let predicate_vars = predicate_vars @@ b1 in
    let subsume_types ctxt ?target_var t1 t2 =
      let (ctxt',t,r') = make_fresh_type ~loc ?target_var ~fv:predicate_vars t1 ctxt in
      let c_up =
        constrain_type ctxt1.path_condition ctxt1.gamma t1 r' ctxt'
        |> constrain_type ctxt2.path_condition ctxt2.gamma t2 r'
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
    match t1,t2 with
    | `UnitT,`UnitT -> (c_sub,`UnitT)
    | (#typ as t1),(#typ as t2) -> ((subsume_types c_sub t1 t2) :> (context * etype))
    | _ -> assert false
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
  let inst ?target_var p = CtxtPred (c.label,p,p_vars,target_var) in
  let subst_type ?target_var t =
    update_refinement (inst ?target_var @@ get_refinement t) t
  in
  let input_env = ctxt.gamma in
  let callee_type = SM.find c.callee ctxt.theta in
  let in_out_types = List.combine callee_type.arg_types callee_type.output_types in
  let updated_ctxt = List.fold_left2 (fun acc (k,arg_t) (in_t,out_t) ->
      let pre_t_ctxt = constrain_var ctxt.path_condition input_env acc k (inst ~target_var:k @@ get_refinement in_t)
        |> constrain_owner arg_t in_t in
      if (post_update_type arg_t) then
        update_type k (subst_type ~target_var:k out_t) pre_t_ctxt
      else
        pre_t_ctxt
    ) ctxt arg_bindings in_out_types
  in
  let result = match callee_type.result_type with
    | None -> None
    | Some t -> Some (subst_type t)
  in
  (updated_ctxt, result)

let process_function_bind ctxt fdef =
  let arg_names = fdef.args in
  let f_typ = SM.find fdef.name ctxt.theta in
  let typ_template = List.combine arg_names f_typ.arg_types in
  let fv = predicate_vars typ_template in
  let init_env = List.map (fun (n,t) ->
      let pred_var = get_refinement t in
      let t' = update_refinement (Pred (pred_var,fv,Some n)) t in
      (n,t')
    ) typ_template |>
      List.fold_left (fun acc (v,ty) ->
        SM.add v ty acc
      ) SM.empty
  in
  let (ctxt',t') = process_expr { ctxt with gamma = init_env } fdef.body in
  let out_typ_template = List.combine arg_names f_typ.output_types in
  let ctxt'' = List.fold_left (fun acc (v,out_ty) ->
      let out_pred = Pred ((get_refinement out_ty),fv,Some v) in
      constrain_var [] acc.gamma acc v out_pred
      |> constrain_owner out_ty (SM.find v acc.gamma)
    ) ctxt' out_typ_template in
  match f_typ.result_type,t' with
  | None,`UnitT -> ctxt''
  | Some ret_templ,(#typ as body_t) ->
    let return_pred = Pred ((get_refinement ret_templ),fv,None) in
    constrain_type [] ctxt''.gamma body_t return_pred ctxt''
  | _ -> assert false

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
  

let infer ~print_pred st (fns,main) =
  let init_fun_type ctxt f_def =
    let gen_refine_templ ?target_var ~loc free_vars t ctxt =
      match t with
      | `Int ->
        let (ctxt',p) = alloc_pred ?target_var ~loc free_vars ctxt in
        (ctxt',(`Int p))
      | `Unit -> assert false
      | `IntRef ->
        let (ctxt',(p,o)) = ((alloc_pred ?target_var ~loc free_vars) >> alloc_ovar) ctxt in
        (ctxt',`Ref (`Int p,o))
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
      match simple_ftype.SimpleTypes.ret_type with
      | `Unit -> (ctxt'',None)
      | rt -> let (ctxt''',t) = (gen_refine_templ ~loc:(LReturn f_def.name) free_vars rt ctxt'') in
        (ctxt''', Some t)
    in
    { ctxt''' with
      theta = SM.add f_def.name {
          arg_types; output_types; result_type
        } ctxt'''.theta
    }
  in
  let initial_ctxt = {
    theta = SM.empty;
    gamma = SM.empty;
    ownership = [];
    ovars = [];
    refinements = [];
    pred_arity = IntMap.empty;
    v_counter = 0;
    pred_detail = Hashtbl.create 10;
    path_condition = []
  } in
  let ctxt = List.fold_left init_fun_type initial_ctxt fns in
  let ctxt' = List.fold_left process_function ctxt fns in
  let (ctxt'',_) = process_expr ctxt' main in
  if print_pred then print_pred_details ctxt''.pred_detail;
  (ctxt''.ownership, ctxt''.ovars, ctxt''.refinements, ctxt''.pred_arity)
  

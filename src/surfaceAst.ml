type op = [
  | `OVar of string
  | `OInt of int
  | `ODeref of string
  | `Nondet
  | `Field of op * string
]

type r_init = [
  op
| `Record of (string * r_init) list
]

type call = string * int * (op list)

type lhs = [
  | op
  | `Mkref of r_init
  | `BinOp of op * string * op
  | `Call of call
]

type relation = {
  op1: op;
  cond: string;
  op2: op
}

type exp =
  | Unit
  | Var of string
  | Int of int
  | Cond of int * [`Var of string | `BinOp of op * string * op] * exp * exp
  | Assign of string * lhs
  | FAssign of string * string * lhs
  | Let of int * string * lhs * exp
  | Alias of int * string * string
  | Assert of relation
  | Call of call
  | Seq of exp * exp

type fn = string * string list * exp
type prog = fn list * exp

module A = Ast

module SS = Set.Make(String)
module SM = StringMap

type field_ctxt = SS.t SM.t

let tvar = Printf.sprintf "__t%d"

let alloc_temp count =
  let v = tvar count in
  (count + 1),v

let mk_simplify_expr fields =
  let rec simplify_expr ?next count e =
    let get_continuation count = match next with
      | None -> simplify_expr count @@ Int 0
      | Some e' -> simplify_expr count e'
    in
    match e with
    | Unit -> simplify_expr count @@ Int 0
    | Var s -> A.EVar s
    | Int i ->
      bind_in count (`OInt i) (fun _ var -> A.EVar var)
    | Cond (i,`Var v,e1,e2) ->
      A.Cond (i,v,simplify_expr count e1,simplify_expr count e2)
    | Cond (i,(`BinOp _ as b),e1,e2) ->
      bind_in ~ctxt:i count (b :> lhs) (fun c tvar ->
          A.Cond (i,tvar,simplify_expr c e1,simplify_expr c e2)
        )
    | Seq (((Assign _ | Alias _ | Assert _) as ue),e1) ->
      simplify_expr ~next:e1 count ue
    | Seq (e1,e2) ->
      A.Seq (simplify_expr count e1,simplify_expr count e2)
    | Assign (v,l) ->
      lift_to_imm count l (fun c i ->
          A.Assign (v,i,get_continuation c)
        )
    | FAssign (b,f,lhs) ->
      lift_to_imm count lhs (fun c i ->
          offset_to_field c b f (fun c' f_var ->
            A.Assign (f_var,i,get_continuation c')
          )
        )
    | Let (i,v,lhs,body) ->
      lift_to_lhs ~ctxt:i count lhs (fun c lhs' ->
          let body' = simplify_expr c body in
          A.Let (i,v,lhs',body')
        )
    | Alias (i,v1,v2) -> 
      A.Alias (i,v1,v2, get_continuation count)
    | Assert { op1; cond; op2 } ->
      lift_to_imm count (op1 :> lhs) (fun c op1' ->
          lift_to_imm c (op2 :> lhs) (fun c' op2' ->
            A.Assert ({ A.rop1 = op1'; A.cond = cond; A.rop2 = op2' }, get_continuation c')
          )
        )
    | Call ((_,i,_) as c) ->
      bind_in ~ctxt:i count (`Call c) (fun _ tvar ->
          A.EVar tvar
        )
  and offset_to_field ?ctxt count var f (rest: int -> string -> A.exp) =
    if (SM.find f fields) = 0 then
      rest count var
    else
      let c,tvar = alloc_temp count in
      let offs = A.PtrArith (var,SM.find f fields) in
      let body = rest c tvar in
      A.Let (LabelManager.register ?ctxt (),tvar,offs,body)
  and lift_to_lhs ?ctxt count (lhs : lhs) (rest: int -> A.lhs -> A.exp) =
    let k r = rest count r in
    match lhs with
    | `Field (b,f_name) ->
      lift_to_var ?ctxt count (b :> lhs) (fun c b_var ->
          offset_to_field ?ctxt c b_var f_name (fun c' f_var ->
            rest c' @@ A.Deref f_var
          )
        )
    | `OVar v -> k @@ A.Var v
    | `OInt i -> k @@ A.Const i
    | `ODeref v -> k @@ A.Deref v
    | `Nondet -> k @@ A.Nondet
    | `Call c ->
      lift_to_call count c (fun c' l -> rest c' @@ A.Call l)
    | `BinOp (o1,op_name,o2) ->
      lift_to_var ?ctxt count (o1 :> lhs) (fun c i1 ->
          lift_to_var c (o2 :> lhs) (fun c' i2 ->
            rest c' (A.Call { A.callee = op_name; arg_names = [i1;i2]; label = LabelManager.register ?ctxt () })
          )
        )
    | `Mkref `Nondet -> k @@ A.Mkref [ A.RNone ]
    | `Mkref (`OInt i) -> k @@ A.Mkref [ (A.RInt i) ]
    | `Mkref (`OVar s) -> k @@ A.Mkref [ (A.RVar s) ]
    | `Mkref (`Record kv_list) ->
      lift_to_tuple ?ctxt count kv_list (fun _ t_list ->
          k @@ A.Mkref t_list
        )
    | `Mkref (#op as o) ->
      bind_in ?ctxt count (o :> lhs) (fun c tvar ->
          rest c @@ A.Mkref [ (A.RVar tvar) ]
        )
  and lift_to_rinit ?ctxt count (r: r_init) rest =
    let k = rest count in
    match r with
    | `Record _ -> bind_in ?ctxt count (`Mkref r) (fun c' var ->
                       rest c' @@ A.RVar var
                     )
    | `Nondet -> k A.RNone
    | `OVar v -> k @@ A.RVar v
    | `OInt i -> k @@ A.RInt i
    | #op as o ->
      bind_in ?ctxt count (o :> lhs) (fun c' var ->
          rest c' @@ A.RVar var
        )
  and sort_fields acc =
    List.fast_sort (fun (k1,_) (k2,_) ->
      (SM.find k1 fields) - (SM.find k2 fields)
    ) acc
    |> List.map snd
  and lift_to_tuple ?ctxt count kv_list rest =
    let rec t_loop c acc kl =
      match kl with
      | [] -> rest c @@ sort_fields acc
      | (k,v)::l -> lift_to_rinit ?ctxt c v (fun c' lifted ->
                        t_loop c' ((k,lifted)::acc) l
                      )
    in
    t_loop count [] kv_list
  and lift_to_var ?ctxt c (h: lhs) rest =
    match h with
    | `OVar v -> rest c v
    | _ -> bind_in ?ctxt c h (fun c' tvar ->
               rest c' tvar
             )
  and lift_to_imm ?ctxt count (o: lhs) rest =
    match o with
    | `OVar s -> rest count @@ A.IVar s
    | `OInt i -> rest count @@ A.IInt i
    | _ -> bind_in ?ctxt count o (fun c tvar ->
               rest c (A.IVar tvar)
             )
  and lift_to_call count (callee,id,args) rest =
    let rec recurse c a k = match a with
      | [] -> k c []
      | h::t -> lift_to_var ~ctxt:id c (h :> lhs) (fun c' var ->
                    recurse c' t (fun c'' l ->
                      k c'' @@ var::l
                    )
                  )
    in
    recurse count args (fun c' l ->
      rest c' { A.callee = callee; A.label = id; A.arg_names = l }
    )
  and bind_in ?ctxt count lhs k =
    lift_to_lhs ?ctxt count lhs (fun c' lhs' ->
      let (c'',tvar) = alloc_temp c' in
      let to_inst = k c'' tvar in
      A.Let (LabelManager.register ?ctxt (),tvar,lhs',to_inst)
    )
  in
  simplify_expr

let add_fields s ctxt =
  let found = SS.fold (fun f stat ->
    let new_cont =
      match SM.mem f ctxt,stat with
      | f,None -> Some f
      | f,Some f' when f <> f' -> failwith "Inconsistent fields"
      | f,Some f' when f = f' -> stat
      | _ -> assert false
    in
    new_cont
    ) s None in
  match found with
  | None -> failwith "empty record"
  | Some true when not (SM.mem (SS.min_elt s) ctxt) ->
    failwith "Inconsisent fields"
  | Some true ->
    let curr_set = ctxt |> SM.find @@ SS.min_elt s in
    if SS.equal curr_set s then
      ctxt
    else
      failwith "Inconsistent fields"
  | Some false -> SM.add (SS.min_elt s) s ctxt

let rec process_rec d ctxt =
  match d with
  | `Record kv_list ->
    let (ss,ctxt') =
      List.fold_left (fun (ss,acc_c) (k,r) ->
        (SS.add k ss, process_rec r acc_c)
      ) (SS.empty,ctxt) kv_list
    in
    add_fields ss ctxt'
  | _ -> ctxt

let rec compute_f e ctxt =
  match e with
  | FAssign _
  | Assert _
  | Call _
  | Unit
  | Alias _
  | Assign _
  | Var _ 
  | Int _ -> ctxt
  | Seq(e1,e2)
  | Cond (_, _, e1, e2) ->
    ctxt
    |> compute_f e1
    |> compute_f e2
  | Let (_,_,`Mkref ((`Record _) as r),e) ->
    process_rec r ctxt
    |> compute_f e
  | Let (_,_,`Mkref _,e) ->
    compute_f e ctxt
  | Let (_,_,_,e) ->
    compute_f e ctxt

type field_offs = int SM.t

let simplify (fns,body) =
  let fields = List.fold_left (fun ct (_,_,e) ->
    compute_f e ct
  ) SM.empty fns
    |> compute_f body
  in
  let offs = SM.fold (fun _ ss acc ->
      SS.elements ss
      |> List.mapi (fun i k -> (i,k))
      |> List.fold_left (fun acc' (i,k) ->
          SM.add k i acc'
        ) acc
    ) fields SM.empty in
  let simplify_expr = mk_simplify_expr offs in
  let simpl_fn = List.map (fun (name,args,e) ->
      { A.name = name; A.args = args; A.body = simplify_expr 0 e }
    ) fns in
  let program_body = simplify_expr 0 body in
  (simpl_fn, program_body)
  

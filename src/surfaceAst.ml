module A = Ast

type lhs = [
  | `OVar of string
  | `OInt of int
  | `ODeref of string
  | `Nondet
  | `BinOp of lhs * string * lhs
  | `Null
  | `OBool of bool
  | `Mkref of lhs
  | `MkArray of lhs
  | `BinOp of lhs * string * lhs
  | `Call of call
  | `Tuple of lhs list
  | `Read of lhs * lhs
] and call = string * int * (lhs list)

type relation = {
  op1: lhs;
  cond: string;
  op2: lhs
}

type patt = A.patt

type exp =
  | Unit of int
  | Value of int * lhs
  | Cond of int * [`Var of string | `BinOp of lhs * string * lhs | `Nondet] * exp * exp
  | NCond of int * string * exp * exp
  | Assign of int * string * lhs
  | Update of int * lhs * lhs * lhs
  | Let of int * patt * lhs * exp
  | Alias of int * string * A.src_ap
  | Assert of int * relation
  | Call of call
  | Seq of exp * exp
  | EAnnot of int * (string * RefinementTypes.typ) list

type fn = string * string list * exp
type prog = fn list * exp

module SS = Set.Make(String)
module SM = StringMap

let tvar = Printf.sprintf "__t%d"

let alloc_temp count =
  let v = tvar count in
  (count + 1),v

let tag_fresh t =
  (LabelManager.register (), t)

let tag_with i t =
  (i, t)  

let rec simplify_expr ?next count e : int * A.raw_exp =
  let get_continuation ~ctxt count = match next with
    | None -> simplify_expr count @@ Value (LabelManager.register ~ctxt (), `OInt 0)
    | Some e' -> simplify_expr count e'
  in
  match e with
  | Unit i -> simplify_expr count @@ Value (i,`OInt 0)
  | Value (i,`OVar v) -> (i,A.EVar v)
  | Value (i,lhs) ->
    bind_in ~ctxt:i count lhs (fun _ tvar ->
        A.EVar tvar |> tag_with i
      )
  | NCond (i,v,e1,e2) ->
    A.NCond (v,simplify_expr count e1,simplify_expr count e2) |> tag_with i
  | Cond (i,`Var v,e1,e2) ->
    A.Cond (v,simplify_expr count e1,simplify_expr count e2) |> tag_with i
  | Cond (i,`Nondet,e1,e2) ->
    bind_in ~ctxt:i count `Nondet (fun c tvar ->
        A.Cond (tvar,simplify_expr c e1,simplify_expr c e2)
        |> tag_with i
      )
  | Cond (i,(`BinOp _ as b),e1,e2) ->
    bind_in ~ctxt:i count (b :> lhs) (fun c tvar ->
        A.Cond (tvar,simplify_expr c e1,simplify_expr c e2)
        |> tag_with i
      )
  | Seq (((Assign _ | Alias _ | Assert _ | EAnnot _ | Update _) as ue),e1) ->
    simplify_expr ~next:e1 count ue
  | Seq (e1,e2) ->
    A.Seq (simplify_expr count e1,simplify_expr count e2)
    |> tag_fresh
  | Assign (id,v,l) ->
    lift_to_imm count l (fun c i ->
        A.Assign (v,i,get_continuation ~ctxt:id c)
        |> tag_with id
      )
  | Update (id,base,ind,lhs) ->
    bind_in ~ctxt:id count base (fun count tvar ->
        lift_to_imm count ind (fun c il ->
          lift_to_imm c lhs (fun c' ll ->
            A.Update (tvar,il,ll,get_continuation ~ctxt:id c')
            |> tag_with id
          )
        )
      )
  | Let (i,v,lhs,body) ->
    lift_to_lhs ~ctxt:i count lhs (fun c lhs' ->
        let body' = simplify_expr c body in
        A.Let (v,lhs',body')
        |> tag_with i
      )
  | Alias (i,v1,v2) -> 
    A.Alias (v1,v2, get_continuation ~ctxt:i count)
    |> tag_with i
  | Assert (i,{ op1; cond; op2 }) ->
    lift_to_imm count (op1 :> lhs) (fun c op1' ->
        lift_to_imm c (op2 :> lhs) (fun c' op2' ->
          A.Assert ({ A.rop1 = op1'; A.cond = cond; A.rop2 = op2' }, get_continuation ~ctxt:i c')
          |> tag_with i
        )
      )
  | Call ((_,i,_) as c) ->
    bind_in ~ctxt:i count (`Call c) (fun _ tvar ->
        A.EVar tvar |> tag_fresh
      )
  | EAnnot (i,g) -> A.EAnnot (g, get_continuation ~ctxt:i count) |> tag_with i

and lift_to_lhs ?ctxt count (lhs : lhs) (rest: int -> A.lhs -> A.exp) =
  let k r = rest count r in
  match lhs with
  | `Null -> k @@ A.Null
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
  | `Mkref lhs ->
    lift_to_rinit ?ctxt count lhs (fun c' r ->
        rest c' @@ A.Mkref r
      )
  | `MkArray lhs ->
    lift_to_var ?ctxt count lhs (fun c i1 ->
        rest c @@ A.MkArray i1
      )
  | `Tuple tl -> lift_to_tuple ?ctxt count tl (fun c' tlist ->
                     rest c' @@ A.Tuple tlist
                   )
  | `Read (base,ind) ->
    lift_to_var ?ctxt count base (fun c b ->
        lift_to_imm ?ctxt c ind (fun c' i ->
          rest c' @@ A.Read (b,i)
        )
      )
  | `OBool f -> k @@ A.Const (if f then 0 else 1)

and lift_to_rinit ?ctxt count (r: lhs) rest =
  let k = rest count in
  match r with
  | `Nondet -> k A.RNone
  | `OVar v -> k @@ A.RVar v
  | `OInt i -> k @@ A.RInt i
  | #lhs as l ->
    bind_in ?ctxt count l (fun c' var ->
        rest c' @@ A.RVar var
      )

and lift_to_tuple ?ctxt count l rest =
  let rec t_loop c acc kl =
    match kl with
    | [] -> rest c @@ List.rev acc
    | v::l -> lift_to_rinit ?ctxt c v (fun c' lifted ->
                      t_loop c' (lifted::acc) l
                    )
  in
  t_loop count [] l
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
and bind_in ?ctxt count lhs (k: int -> string -> A.exp) =
  lift_to_lhs ?ctxt count lhs (fun c' lhs' ->
    let (c'',tvar) = alloc_temp c' in
    let to_inst = k c'' tvar in
    A.Let (A.PVar tvar,lhs',to_inst) |> tag_with @@ LabelManager.register ?ctxt ()
  )

let simplify (fns,body) =
  let simpl_fn = List.map (fun (name,args,e) ->
      { A.name = name; A.args = args; A.body = simplify_expr 0 e }
    ) fns in
  let program_body = simplify_expr 0 body in
  (simpl_fn, program_body)
  

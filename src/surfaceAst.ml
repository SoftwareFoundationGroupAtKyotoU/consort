(* The surface AST represents the "friendlier" surfact syntax in which IMP programs
   can be written. The parser (see parser.mly) constructs terms in this syntax,
   which is then (straightforwardly) translated into the low-level, (roughly)
   three address form expected by Consort.

   The key differences between the surface syntax and the low-level AST syntax are
   as follows:

   + Unit's meaning is different. Unit in the surface syntax may appear in a tail position,
   indicating that the function returns no useful information. In such a case, it is actually
   translated into a "return 0" (as we do not have a unit type). In contrast, Unit may NOT appear
   in a tail position in the low-level syntax, as every tail position must either be a fail or explicit return.
   Unit is only used in non-trail positions as a leaf node to indicate "no more computation" when the grammar
   demands an expression, i.e., after an assignment, as a branch of a conditional etc.
   + As hinted above, all expressions in a tail position are lifted into an explicit return statement
   + Assign, Update, and friends do NOT require a continuation in the surface syntax. If they are sequenced
   with something, then the remainder of that sequence is shifted into the continuation in the low-level syntax. Otherwise
   a dummy continuation is inserted.

   A comical note: I got left and right confused, so what I call an LHS is really supposed to be an RHS. I may fix
   that in my copious free time...
*)

module A = Ast

type lhs = [
  | `OVar of string
  | `OInt of int
  | `ODeref of string
  | `Nondet of RefinementTypes.concr_refinement option
  | `BinOp of lhs * string * lhs
  | `Null
  | `OBool of bool
  | `Mkref of lhs
  | `MkArray of lhs
  | `BinOp of lhs * string * lhs
  | `Call of call
  | `Tuple of lhs list
  | `Read of lhs * lhs
  | `LengthOf of lhs
  | `Nil
  | `Cons of lhs * lhs
] and call = string * int * (lhs list)

type relation = {
  op1: lhs;
  cond: string;
  op2: lhs
}

type patt = A.patt

type pos = A.position

type exp =
  | Unit of pos
  | Fail of pos
  | Value of pos * lhs
  | Cond of pos * [`Var of string | `BinOp of lhs * string * lhs | `Nondet | `Call of call] * exp * exp
  | NCond of pos * string * exp * exp
  | Assign of pos * string * lhs
  | Update of pos * lhs * lhs * lhs
  | Let of pos * patt * lhs * exp
  | Alias of pos * Paths.concr_ap * Paths.concr_ap
  | Assert of pos * relation
  | Seq of Lexing.position * exp * exp
  | Return of pos * lhs
  | Match of pos * lhs * exp * string * string * exp

type fn = string * string list * exp
type prog = fn list * exp

module SS = Set.Make(String)
module SM = StringMap

let tvar = Printf.sprintf "__t%d"

let alloc_temp count =
  let v = tvar count in
  (count + 1),v

let tag_fresh pos t =
  (LabelManager.register pos, t)

let tag_with i t =
  (i, t)  

(** NK: added **)
let sanity_check_alias (v1:Paths.path) (v2:Paths.path) =
  let (root1,_,_)= (v1 :> Paths.root * Paths.steps list * Paths.suff) in
  let (root2,_,_)= (v2 :> Paths.root * Paths.steps list * Paths.suff) in
  if root1=root2 then
    (print_string "Warning: found an alias statement that contains more than one occurrence of the same variable.\nThe analysis may be unsound\n";flush stdout)

(* This rewriting is fairly standard, but it helps to understand some key components.
   First, count determines the number of temporary variables in scope, this ensures
   temporary variables are unique when they are created. This count is thus threaded through
   the lifting process, being incremented as necessary. Notice that we can reuse
   temporary variable names when we are guaranteed the original use is out of scope,
   a nice invariant provided by the lifting is that if count = n, then any variables generated with
   ids >= n must not be in scope.
*)
let rec simplify_expr ?next ~is_tail count e : pos * A.raw_exp =
  let get_continuation ~ctxt count = match next with
    | None -> simplify_expr ~is_tail count @@ Value (LabelManager.register_with ctxt, `OInt 0)
    | Some e' -> simplify_expr ~is_tail count e'
  in
  match e with
  | Fail i -> A.Fail |> tag_with i
  | Unit i ->
    if is_tail then
      simplify_expr ~is_tail count @@ Value (i,`OInt 0)
    else
      A.Unit |> tag_with i
  | Value (i, v) ->
    if is_tail then
      (* lift_to_var (or lift_to_imm or lift_to_lhs) 
         lift complicated expressions to the required form,
         introducing temporary variables as necessary. They all take a continuation,
         passing in the value in the desired form (var, imm, lhs, etc.) and the current temp var counter.

         The common feature of these is found in bind_in, which actually handles the instrumentation with
         temporary variables.
      *)
      lift_to_var ~ctxt:i count v (fun _ tvar ->
        A.Return tvar |> tag_with i
      )
    else
      lift_to_var ~ctxt:i count v (fun _ _tvar ->
        A.Unit |> tag_with i
      )
  | NCond (i,v,e1,e2) ->
    A.NCond (v,simplify_expr ~is_tail count e1,simplify_expr ~is_tail count e2) |> tag_with i
  | Cond (i,`Var v,e1,e2) ->
    A.Cond (v,simplify_expr ~is_tail count e1,simplify_expr ~is_tail count e2) |> tag_with i
  | Cond (i,`Nondet,e1,e2) ->
    bind_in ~ctxt:i count (`Nondet None) (fun c tvar ->
        A.Cond (tvar,simplify_expr ~is_tail c e1,simplify_expr ~is_tail c e2)
        |> tag_with i
      )
  | Cond (i, `Call c, e1, e2) ->
    bind_in ~ctxt:i count (`Call c) (fun c tvar ->
        A.Cond (tvar, simplify_expr ~is_tail c e1, simplify_expr ~is_tail c e2)
        |> tag_with i
      )
  | Cond (i,(`BinOp _ as b),e1,e2) ->
    bind_in ~ctxt:i count (b :> lhs) (fun c tvar ->
        A.Cond (tvar,simplify_expr ~is_tail c e1,simplify_expr ~is_tail c e2)
        |> tag_with i
      )
  | Seq (_,((Assign _ | Alias _ | Assert _ | Update _) as ue),e1) ->
    simplify_expr ~next:e1 ~is_tail count ue
  | Seq (pos,e1,e2) ->
    A.Seq (simplify_expr ~is_tail:false count e1,simplify_expr ~is_tail count e2)
    |> tag_fresh pos
  | Assign (id,v,l) ->
    lift_to_imm ~ctxt:id count l (fun c i ->
        A.Assign (v,i,get_continuation ~ctxt:id c)
        |> tag_with id
      )
  | Update (id,base,ind,lhs) ->
    lift_to_var ~ctxt:id count base (fun count tvar ->
        lift_to_var ~ctxt:id count ind (fun c ivar ->
          lift_to_var ~ctxt:id c lhs (fun c' lvar ->
            A.Update (tvar,ivar,lvar,get_continuation ~ctxt:id c')
            |> tag_with id
          )
        )
      )
  | Let (i,v,lhs,body) ->
    lift_to_lhs ~ctxt:i count lhs (fun c lhs' ->
        let body' = simplify_expr ~is_tail c body in
        A.Let (v,lhs',body')
        |> tag_with i
      )
  | Alias (i,v1,v2) -> 
     sanity_check_alias v1 v2; (* NK: added *)
    A.Alias (v1,v2, get_continuation ~ctxt:i count)
    |> tag_with i
  | Assert (i,{ op1; cond; op2 }) ->
    lift_to_imm ~ctxt:i count (op1 :> lhs) (fun c op1' ->
        lift_to_imm ~ctxt:i c (op2 :> lhs) (fun c' op2' ->
          A.Assert ({ A.rop1 = op1'; A.cond = cond; A.rop2 = op2' }, get_continuation ~ctxt:i c')
          |> tag_with i
        )
      )
  | Return (i,rval) ->
    lift_to_var ~ctxt:i count rval (fun _ tvar ->
        A.Return tvar |> tag_with i
      )
  | Match (i, e1, e2, h, r, e3) ->
    lift_to_lhs ~ctxt:i count e1 (fun c e1' ->
        A.Match (e1', simplify_expr ~is_tail c e2, h, r, simplify_expr ~is_tail c e3)
        |> tag_with i
      )

and lift_to_lhs ~ctxt count (lhs : lhs) (rest: int -> A.lhs -> A.exp) =
  let k r = rest count r in
  match lhs with
  | `Null -> k @@ A.Null
  | `OVar v -> k @@ A.Var v
  | `OInt i -> k @@ A.Const i
  | `ODeref v -> k @@ A.Deref v
  | `Nondet r -> k @@ A.Nondet r
  | `LengthOf lhs ->
    lift_to_var ~ctxt count lhs (fun c' r ->
        rest c' @@ A.LengthOf r
      )
  | `Call c ->
    lift_to_call ~ctxt count c (fun c' l -> rest c' @@ A.Call l)
  | `BinOp (o1,op_name,o2) ->
    lift_to_var ~ctxt count (o1 :> lhs) (fun c i1 ->
        lift_to_var ~ctxt c (o2 :> lhs) (fun c' i2 ->
          rest c' (A.Call { A.callee = op_name; arg_names = [i1;i2]; label = LabelManager.register_with ctxt |> fst })
        )
      )
  | `Mkref lhs ->
    lift_to_rinit ~ctxt count lhs (fun c' r ->
        rest c' @@ A.Mkref r
      )
  | `MkArray lhs ->
    lift_to_var ~ctxt count lhs (fun c i1 ->
        rest c @@ A.MkArray i1
      )
  | `Tuple tl -> lift_to_tuple ~ctxt count tl (fun c' tlist ->
                     rest c' @@ A.Tuple tlist
                   )
  | `Read (base,ind) ->
    lift_to_var ~ctxt count base (fun c b ->
        lift_to_var ~ctxt c ind (fun c' i ->
          rest c' @@ A.Read (b,i)
        )
      )
  | `OBool f -> k @@ A.Const (if f then 0 else 1)
  | `Cons _ -> assert false
  | `Nil -> k @@ A.Nil

and lift_to_rinit ~ctxt count (r: lhs) rest =
  let k = rest count in
  match r with
  | `Nondet None -> k A.RNone
  | `OVar v -> k @@ A.RVar v
  | `OInt i -> k @@ A.RInt i
  | #lhs as l ->
    bind_in ~ctxt count l (fun c' var ->
        rest c' @@ A.RVar var
      )

and lift_to_tuple ~ctxt count l rest =
  let rec t_loop c acc kl =
    match kl with
    | [] -> rest c @@ List.rev acc
    | v::l -> lift_to_rinit ~ctxt c v (fun c' lifted ->
                      t_loop c' (lifted::acc) l
                    )
  in
  t_loop count [] l
and lift_to_var ~ctxt c (h: lhs) rest =
  match h with
  | `OVar v -> rest c v
  | _ -> bind_in ~ctxt c h (fun c' tvar ->
             rest c' tvar
           )
and lift_to_imm ~ctxt count (o: lhs) rest =
  match o with
  | `OVar s -> rest count @@ A.IVar s
  | `OInt i -> rest count @@ A.IInt i
  | _ -> bind_in ~ctxt count o (fun c tvar ->
             rest c (A.IVar tvar)
           )
and lift_to_call ~ctxt count (callee,id,args) rest =
  let rec recurse c a k = match a with
    | [] -> k c []
    | h::t -> lift_to_var ~ctxt c (h :> lhs) (fun c' var ->
                  recurse c' t (fun c'' l ->
                    k c'' @@ var::l
                  )
                )
  in
  recurse count args (fun c' l ->
    rest c' { A.callee = callee; A.label = id; A.arg_names = l }
  )
  (* Bind the lhs to a temporary variable, and then
     call k with the current temp count, the variable name. k is expected
     to produce an expression; bind_in wraps that expression
     with a let expression bindings the temporary variable.
     
     Notice that lift_to_lhs (used by bind_in) is mutually recursive
     with bind_in; when simplifying an lhs, we may need to bind subexpressions
     to temporary variables, which themselves may require further simplification, etc. etc.
     Ultimately, this process bottoms out at immediate expressions, literal integers or variables
     which are base cases for this lifting process. The use of continuations (and intercission by
     bind_in) guarantees that these "intermediate" temporary variables are bound in the correct order.
  *)
and bind_in ~ctxt count lhs (k: int -> string -> A.exp) =
  lift_to_lhs ~ctxt count lhs (fun c' lhs' ->
    let (c'',tvar) = alloc_temp c' in
    let to_inst = k c'' tvar in
    A.Let (A.PVar tvar,lhs',to_inst) |> tag_with @@ LabelManager.register_with ctxt
  )

let simplify (fns,body) =
  let simpl_fn = List.map (fun (name,args,e) ->
      { A.name = name; A.args = args; A.body = simplify_expr ~is_tail:true 0 e }
    ) fns in
  let program_body = simplify_expr ~is_tail:false 0 body in
  (simpl_fn, program_body)
  

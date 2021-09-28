open Ast
open PrettyPrint

(* values *)
type v =
  | IntV of int
  | NilV
  | RefV of v ref
  | ArrayV of v array
  | TupleV of v list

let rec pp_val = function
  | IntV i -> pi i
  | NilV -> ps "null"
  | RefV v ->
     pl [
         ps "ref ";
         pp_val !v
       ]
  | ArrayV arr ->
     pl [
         ps "[|";
         psep "; " @@ Array.to_list @@ Array.map pp_val arr;
         ps "|]"
       ]
  | TupleV [] -> assert false
  | TupleV vs ->
     pl [
         ps "(";
         psep ", " @@ List.map pp_val vs;
         ps ")"
       ]

exception NotImplemented of string

type env = (string * v) list

let rec lookup_fundef f = function
  | [] -> assert false
  | { name = g; args = params; body = e} :: rest ->
     if f = g then (params, e)
     else lookup_fundef f rest

let empty_env = []
let lookup = List.assoc
let rec extend patt valu env =
  match patt with
  | PVar id -> (id, valu) :: env
  | PTuple pats ->
     begin match valu with
     | TupleV vs -> List.fold_right2 extend pats vs env
     | _ -> assert false
     end
  | PNone -> env

let intV_of_bool b =
  if b then IntV 1 else IntV 0

let intrinsic_funs = [
    ("!=", function [IntV i1; IntV i2] -> intV_of_bool @@ (i1 <> i2) | _ -> assert false);
    ("%", function [IntV i1; IntV i2] -> IntV (i1 mod i2) | _ -> assert false);
    ("&&", function [IntV i1; IntV i2] -> intV_of_bool ((i1 <> 0) && (i2 <> 0)) | _ -> assert false);
    ("*", function [IntV i1; IntV i2] -> IntV (i1 * i2) | _ -> assert false);
    ("+", function [IntV i1; IntV i2] -> IntV (i1 + i2) | _ -> assert false);
    ("-", function [IntV i1; IntV i2] -> IntV (i1 - i2) | _ -> assert false);
    ("<", function [IntV i1; IntV i2] -> intV_of_bool (i1 < i2) | _ -> assert false);
    ("<=", function [IntV i1; IntV i2] -> intV_of_bool (i1 <= i2) | _ -> assert false);
    ("=", function [IntV i1; IntV i2] -> intV_of_bool (i1 = i2) | _ -> assert false);
    (">", function [IntV i1; IntV i2] -> intV_of_bool (i1 > i2) | _ -> assert false);
    (">=", function [IntV i1; IntV i2] -> intV_of_bool (i1 >= i2) | _ -> assert false);
    ("||", function [IntV i1; IntV i2] -> intV_of_bool ((i1 <> 0) || (i2 <> 0)) | _ -> assert false);
  ]

let eval_imm_op env = function
  | IVar id -> lookup id env
  | IInt i -> IntV i

let eval_ap env (p : Paths.concr_ap) =
  let rec follow_step v = function
    | [] -> v
    | `Deref :: rest -> (match follow_step v rest with RefV r -> !r | _ -> assert false)
    | `Proj i :: rest -> (match follow_step v rest with TupleV tp -> List.nth tp i | _ -> assert false)
    | _ -> assert false
  in
  match (p :> Paths.root * Paths.steps list * Paths.suff) with
  | (Paths.Var id, steps, _) -> follow_step (lookup id env) steps
  | _ -> assert false

let rec eval_refine env =
  let open RefinementTypes in
  function
  | Top -> (fun _ -> true)
  | ConstEq n -> (fun i -> i = n)
  | And(r1, r2) -> (fun i -> eval_refine env r1 i && eval_refine env r2 i)
  | Relation {rel_cond; rel_op2; _} ->
     (fun i ->
       let j =
         match rel_op2 with
         | RAp ap -> eval_ap env ap
         | RConst j -> IntV j
       in
       try
         IntV 0 <> List.assoc rel_cond intrinsic_funs [IntV i; j]
       with
       | Not_found -> assert false)
  | NamedPred _ -> raise (NotImplemented "named predicate in the condition")

let rec really_read_int env condopt =
  match read_int(), condopt with
  | i, None -> i
  | i, Some cond ->
     if eval_refine env cond i then i
     else
       begin
         Printf.eprintf "Condition violated! Give me another integer: ";
         flush stderr;
         really_read_int env condopt
       end
  | exception Failure _ ->
     begin
       Printf.eprintf "It's not an integer! Give me an INTEGER: ";
       flush stderr;
       really_read_int env condopt
     end

let eval_ref_contents loc contents env = match contents with
  | RNone ->
     Printf.eprintf "%s: Give me an integer: " (Locations.string_of_location loc);
     flush stderr;
     IntV (really_read_int env None)
  | RInt i -> IntV i
  | RVar id -> lookup id env

let eval_exp fundecls =
  let rec aux env = function
    | (_, Unit None) -> IntV 0
    | (_, Unit (Some id)) -> lookup id env
    | ((_,loc), Fail) -> Locations.raise_errorf ~loc "Fail"
    | (_, Cond (var, then_exp, else_exp)) ->
       begin match lookup var env with
       | IntV 0 -> aux env else_exp
       | IntV _ -> aux env then_exp
       | _ -> assert false
       end
    | (_, NCond (var, then_exp, else_exp)) ->
       begin match lookup var env  with
       | NilV -> aux env then_exp
       | RefV _ -> aux env else_exp
       | _ -> assert false
       end
    | (_, Seq (exp1, exp2)) ->
       ignore(aux env exp1);
       aux env exp2
    | ((_,loc), Assign (var1, rhs, exp')) ->
       begin match lookup var1 env with
       | RefV r -> r := eval_imm_op env rhs; aux env exp'
       | NilV -> Locations.raise_errorf ~loc "NullPointerException"
       | _ -> assert false
       end
    | ((_,loc), Let (pat, rhs, exp')) ->
       let res =
         match rhs with
         | Var id -> lookup id env
         | Const i -> IntV i
         | Mkref init -> RefV (ref (eval_ref_contents loc init env))
         | MkArray id ->
            begin match lookup id env with
            | IntV len -> ArrayV (Array.make len (IntV 0))
            | _ -> assert false
            end
         | Call {callee=f; arg_names=xs; _} ->
            let args = List.map (fun id -> lookup id env) xs in
            begin
              try List.assoc f intrinsic_funs args with
                Not_found ->
                let params, body = lookup_fundef f fundecls in
                let newenv = List.fold_right2 (fun p v env -> (p, v)::env) params args env in
                aux newenv body
            end
         | Deref id ->
            begin match lookup id env with
            | NilV -> Locations.raise_errorf ~loc "NullPointerException"
            | RefV r -> !r
            | _ -> assert false
            end
         | Tuple contents -> TupleV (List.map (fun c -> eval_ref_contents loc c env) contents)
         | Nondet cond ->
            Printf.eprintf "%s: Give me an integer: " (Locations.string_of_location loc);
            flush stderr;
            IntV (really_read_int env cond)
         | Read (id1, id2) ->
            begin match lookup id1 env, lookup id2 env with
            | ArrayV arr, IntV ind -> arr.(ind)
            | _ -> assert false
            end
         | LengthOf id ->
            begin match lookup id env with
            | ArrayV arr -> IntV (Array.length arr)
            | _ -> assert false
            end
         | Null -> NilV
       in
       let newenv = extend pat res env in
       aux newenv exp'
    | (_, Update (base, ind, rhs, exp')) ->
       begin match lookup base env, lookup ind env, lookup rhs env with
       | ArrayV arr, IntV i, v -> arr.(i) <- v; aux env exp'
       | _ -> assert false
       end
    | ((_, loc), Alias (ap1, ap2, exp')) ->
       begin match eval_ap env ap1, eval_ap env ap2 with
       |  RefV r1, RefV r2 -> if r1 == r2 then aux env exp'
                              else Locations.raise_errorf ~loc "Alias Failure"
       | _ -> assert false
       end
    | ((_, loc), Assert ({rop1; cond; rop2}, exp')) ->
       begin match
         List.assoc cond intrinsic_funs [eval_imm_op env rop1; eval_imm_op env rop2]
       with
       | IntV 0 -> Locations.raise_errorf ~loc "Assertion Failure"
       | exception Not_found -> assert false
       | _ ->  aux env exp'
       end
    | (_, Return var) -> lookup var env
  in aux

let eval_prog (fundecls, main) = eval_exp fundecls empty_env main

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

exception Failure
exception NullPointerExc
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

let eval_ref_contents contents env = match contents with
  | RNone -> raise @@ NotImplemented "eval_ref_contents: RNone"
  | RInt i -> IntV i
  | RVar id -> lookup id env

let eval_exp fundecls =
  let rec aux env = function
    | Unit None -> IntV 0
    | Unit (Some id) -> lookup id env
    | Fail -> raise Failure
    | Cond (var, (_, then_exp), (_, else_exp)) ->
       begin match lookup var env with
       | IntV 0 -> aux env else_exp
       | IntV _ -> aux env then_exp
       | _ -> assert false
       end
    | NCond (var, (_, then_exp), (_, else_exp)) ->
       begin match lookup var env  with
       | NilV -> aux env then_exp
       | RefV _ -> aux env else_exp
       | _ -> assert false
       end
    | Seq ((_, exp1), (_, exp2)) ->
       ignore(aux env exp1);
       aux env exp2
    | Assign (var1, rhs, (_, exp')) ->
       begin match lookup var1 env, rhs with
       | RefV r, IVar var2 -> r := lookup var2 env; aux env exp'
       | RefV r, IInt i -> r := IntV i; aux env exp'
       | NilV, _ -> raise NullPointerExc
       | _ -> assert false
       end
    | Let (pat, rhs, (_, exp')) ->
       let res =
         match rhs with
         | Var id -> lookup id env
         | Const i -> IntV i
         | Mkref init -> RefV (ref (eval_ref_contents init env))
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
                aux newenv (snd body)
            end
         | Deref id ->
            begin match lookup id env with
            | NilV -> raise NullPointerExc
            | RefV r -> !r
            | _ -> assert false
            end
         | Tuple contents -> TupleV (List.map (fun c -> eval_ref_contents c env) contents)
         | Nondet _ -> raise @@ NotImplemented "eval_exp: Let-Nondet"
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
    | Update (base, ind, rhs, (_, exp')) ->
       begin match lookup base env, lookup ind env, lookup rhs env with
       | ArrayV arr, IntV i, v -> arr.(i) <- v; aux env exp'
       | _ -> assert false
       end
    | Alias _ (* of Paths.concr_ap * Paths.concr_ap * exp *) -> raise @@ NotImplemented "eval_exp: Alias"
    | Assert _ (* of relation * exp *) -> raise @@ NotImplemented "eval_exp: Assert"
    | Return var -> lookup var env
  in aux

let eval_prog (fundecls, main) = eval_exp fundecls empty_env (snd main)

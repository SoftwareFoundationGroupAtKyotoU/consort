open Ast
open Sexplib.Std

type pred_loc =
  | LCond of int
  | LArg of string
  | LReturn of string
  | LOutput of string
  | LAlias of int
  | LLet of int


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
  rel_cond: string;
  rel_op2: imm_op;
} [@@deriving sexp]


(* 
Pred n,l: A predicate symbol with name n over variables l (nu is implicit)
CtxtPred c,n,l: A Preciate symbol with name n over variables l with explicit context c
Top: unconstrained
Const: the constaint constraint
Eq: equality with variable b
*)
type refinement =
  | Pred of int * string list * string option
  | CtxtPred of int * int * string list * string option
  | Top
  | ConstEq of int
  | Relation of refinement_rel
  | And of refinement * refinement
  | NamedPred of string * string list * string option [@@deriving sexp]

type ownership =
    OVar of int
  | OConst of float[@@deriving sexp]

type 'a ref_contents = [ `Int of 'a ] [@@deriving sexp]

type 'a _typ = [
  | `Int of 'a
  | `Ref of 'a ref_contents * ownership
][@@deriving sexp]

type arg_refinment =
  | InfPred of int
  | BuiltInPred of string
  | True[@@deriving sexp]

type typ = refinement _typ [@@deriving sexp]
type ftyp = arg_refinment  _typ[@@deriving sexp]

type funtype = {
  arg_types: ftyp list;
  output_types: ftyp list;
  result_type: ftyp
}[@@deriving sexp]

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

let ref_of t1 o =
  match t1 with
  | `Ref _ -> failwith "Can't have reference to t"
  | `Int _ as t -> `Ref (t,o)

let to_simple_type = function
  | `Ref (`Int _,_) -> `IntRef
  | `Int _ -> `Int

let to_simple_funenv = StringMap.map (fun { arg_types; result_type; _ } ->
    {
      SimpleTypes.arg_types = List.map to_simple_type arg_types;
      SimpleTypes.ret_type = to_simple_type result_type;
    })
  

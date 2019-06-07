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
                                   (*  | NamedPred of string * string list*)

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

type funtype = {
  arg_types: ftyp list;
  output_types: ftyp list;
  result_type: ftyp
}

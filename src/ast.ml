open Sexplib.Std

type ref_contents =
  | RNone
  | RInt of int
  | RVar of string

type ref_init = ref_contents
  
type fn_call = {
  callee: string;
  arg_names: string list;
  label: int;
}

type imm_op =
    IVar of string
  | IInt of int [@@deriving sexp]

type lhs =
  | Var of string
  | Const of int
  | Mkref of ref_init
  | MkArray of string
  | Call of fn_call
  | Deref of string
  | Tuple of ref_contents list
  | Nondet of RefinementTypes.symbolic_refinement option
  | Read of string * string
  | LengthOf of string
  | Null

type patt =
  | PVar of string
  | PTuple of patt list
  | PNone

type relation = {
  rop1: imm_op;
  cond: string;
  rop2: imm_op
}

type position = int * Lexing.position

type src_ap =
  | AVar of string
  | AProj of string * int
  | ADeref of string
  | APtrProj of string * int

type raw_exp =
  | EVar of string
  | Cond of string * exp * exp
  | NCond of string * exp * exp
  | Seq of exp * exp
  | Assign of string * imm_op * exp
  | Update of string * string * string * exp
  | Let of patt * lhs * exp
  | Alias of string * src_ap * exp
  | Assert of relation * exp
  | EAnnot of (string * RefinementTypes.src_typ) list * exp
and exp = position * raw_exp

type fn = { name: string; args: (string list); body: exp }

type prog = fn list * exp

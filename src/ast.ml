open Sexplib.Std

type ref_contents =
  | RNone
  | RInt of int
  | RVar of string [@@deriving sexp]

type ref_init = ref_contents [@@deriving sexp]
  
type fn_call = {
  callee: string;
  arg_names: string list;
  label: int;
} [@@deriving sexp]

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
  | Null [@@deriving sexp]

type patt =
  | PVar of string
  | PTuple of patt list
  | PNone [@@deriving sexp]

type relation = {
  rop1: imm_op;
  cond: string;
  rop2: imm_op
} [@@deriving sexp]

type position = int * Lexing.position
let sexp_of_position (id,pos) =
  let open Sexplib.Sexp in
  List [ [%sexp_of: int] id; Locations.sexp_of_location pos]

let position_of_sexp sexp =
  let open Sexplib.Sexp in
  match sexp with
  | List [ id; pos ] ->
    ([%of_sexp: int] id, Locations.location_of_sexp pos)
  | _ -> Sexplib.Conv_error.tuple_of_size_n_expected "position" 2 sexp

type src_ap =
  | AVar of string
  | AProj of string * int
  | ADeref of string
  | APtrProj of string * int [@@deriving sexp]

type raw_exp =
  | EVar of string
  | Cond of string * exp * exp
  | NCond of string * exp * exp
  | Seq of exp * exp
  | Assign of string * imm_op * exp
  | Update of string * string * string * exp
  | Let of patt * lhs * exp
  | Alias of string * src_ap * exp
  | Assert of relation * exp [@@deriving sexp]

and exp = position * raw_exp [@@deriving sexp]

type fn = { name: string; args: (string list); body: exp } [@@deriving sexp]

type prog = fn list * exp [@@deriving sexp]

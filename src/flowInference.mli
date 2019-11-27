module P = Paths
module RT = RefinementTypes


type fltype
val fltype_to_string : fltype -> string

type z3_types =
  | ZBool
  | ZInt

type relation = string * (P.concr_ap * z3_types) list

type state_snapshot = {
  mu_relations : relation P.PathMap.t;
  gamma : (string * fltype) list;
  relation : relation
}

type concr_arg =
  | Ap of P.concr_ap
  | BConst of bool
  | IConst of int
  | NondetChoice of concr_arg list
  | KeyedChoice of P.concr_ap * concr_arg * concr_arg [@@deriving sexp]

type clause =
  | PRelation of relation * ((P.concr_ap * concr_arg) list) * int option
  | Relation of (concr_arg,concr_arg) RT.relation * z3_types
  | NamedRel of string * (concr_arg list)
  | NullCons of concr_arg * concr_arg

val infer :
  bif_types:(RefinementTypes.funtype StringMap.t) ->
  SimpleTypes.funtyp StringMap.t * SimpleChecker.SideAnalysis.results ->
  float OwnershipInference.ownership_ops ->
  Ast.fn list * Ast.exp ->
  relation list * (clause list * clause) list * state_snapshot Std.IntMap.t * string

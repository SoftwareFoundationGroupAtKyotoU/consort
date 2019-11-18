module P = Paths
module RT = RefinementTypes

type z3_types =
  | ZBool
  | ZInt

type flow =
  | Havoc of P.concr_ap
  | Copy of P.concr_ap * P.concr_ap
  | Const of P.concr_ap * int
  | NullConst of P.concr_ap * bool

type relation = string * (P.concr_ap * z3_types) list

type concr_arg =
  | Ap of P.concr_ap
  | BConst of bool
  | IConst of int
  | NondetChoice of concr_arg list
  | KeyedChoice of P.concr_ap * concr_arg * concr_arg

type clause =
  | PRelation of relation * ((P.concr_ap * concr_arg) list) * int option
  | Relation of (concr_arg,concr_arg) RT.relation
  | NamedRel of string * (concr_arg list)
  | NullCons of P.concr_ap * P.concr_ap

val infer :
  bif_types:(RefinementTypes.funtype StringMap.t) ->
  SimpleTypes.funtyp StringMap.t * SimpleChecker.SideAnalysis.results ->
  float OwnershipInference.ownership_ops ->
  Ast.fn list * Ast.exp ->
  relation list * (clause list * clause) list * string

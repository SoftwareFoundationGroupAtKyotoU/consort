open RefinementTypes

type funenv = funtype StringMap.t
type oante =
  | ORel of ownership * [ `Eq | `Ge | `Gt ] * float
  | OAny of oante list [@@deriving sexp]
type tenv = typ StringMap.t

type ocon =
    Write of ownership
  | Live of ownership
  | Shuff of (ownership * ownership) *
    (ownership * ownership)
  | Split of ownership *
    (ownership * ownership)
  | Eq of ownership * ownership
  | Wf of ownership * ownership [@@deriving sexp]

type tcon = {
  env : (Paths.concr_ap * concr_refinement * (concr_nullity list)) list;
  ante : concr_refinement;
  conseq : concr_refinement;
  owner_ante : oante list;
  nullity: concr_nullity list;
  target : Paths.concr_ap option
}

type ownership_type = (unit,float,unit,nullity) _typ
type o_theta = ownership_type _funtype StringMap.t
type o_solution = ((int,ownership_type StringMap.t) Hashtbl.t * o_theta)
type type_hints = int -> (SimpleTypes.r_typ StringMap.t) option

module Result :
  sig
    type t = {
      theta : funenv;
      ownership : ocon list;
      ovars : int list;
      refinements : tcon list;
      arity : (bool * int) StringMap.t;
      ty_envs: (int,tenv) Hashtbl.t
    }
  end

val infer :
  print_pred:bool ->
  save_types:bool ->
  ?o_solve:o_solution ->
  intrinsics:funenv ->
  SimpleChecker.simple_results -> Ast.fn list * Ast.exp -> Result.t

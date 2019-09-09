open RefinementTypes

type funenv = funtype StringMap.t
type tenv = typ StringMap.t

type tcon = {
  env : (Paths.concr_ap * concr_refinement * (concr_nullity list)) list;
  ante : concr_refinement;
  conseq : concr_refinement;
  nullity: concr_nullity list;
  target : Paths.concr_ap option
}

module Result :
  sig
    type t = {
      theta : funenv;
      refinements : tcon list;
      arity : (bool * int) StringMap.t;
      ty_envs: (int,tenv) Hashtbl.t
    }
  end

val infer :
  save_types:bool ->
  intrinsics:funenv ->
  SimpleChecker.simple_results ->
  float OwnershipInference.ownership_ops ->
  Ast.fn list * Ast.exp -> Result.t

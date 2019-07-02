module IntMap : Map.S with type key = int

type funenv = RefinementTypes.funtype StringMap.t
type oante = RefinementTypes.ownership * [ `Eq | `Ge | `Gt ] * float

type ocon =
    Write of RefinementTypes.ownership
  | Live of RefinementTypes.ownership
  | Shuff of (RefinementTypes.ownership * RefinementTypes.ownership) *
    (RefinementTypes.ownership * RefinementTypes.ownership)
  | Split of RefinementTypes.ownership *
    (RefinementTypes.ownership * RefinementTypes.ownership)
  | Eq of RefinementTypes.ownership * RefinementTypes.ownership
type tcon = {
  env : (Paths.concr_ap * RefinementTypes.concr_refinement) list;
  ante : RefinementTypes.concr_refinement;
  conseq : RefinementTypes.concr_refinement;
  owner_ante : oante list;
}
module Result :
  sig
    type t = {
      theta : funenv;
      ownership : ocon list;
      ovars : int list;
      refinements : tcon list;
      arity : int IntMap.t;
    }
  end
val infer :
  print_pred:bool ->
  intrinsics:funenv ->
  SimpleTypes.funtyp StringMap.t -> Ast.fn list * Ast.exp -> Result.t

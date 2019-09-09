
module SideAnalysis: sig
  type results = {
    unfold_locs: Std.IntSet.t;
    fold_locs: Std.IntSet.t;
    let_types: SimpleTypes.r_typ Std.IntMap.t
  }
end

type simple_results = SimpleTypes.funtyp StringMap.t * SideAnalysis.results

val typecheck_prog: SimpleTypes.funtyp StringMap.t -> Ast.prog -> simple_results

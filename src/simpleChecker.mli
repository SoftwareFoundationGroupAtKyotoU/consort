
module SideAnalysis: sig
  type results = {
    unfold_locs: Std.IntSet.t;
    fold_locs: Std.IntSet.t
  }
end

type simple_results = SimpleTypes.funtyp StringMap.t* (int -> (SimpleTypes.r_typ StringMap.t) option) * SideAnalysis.results

val typecheck_prog: SimpleTypes.funtyp StringMap.t -> Ast.prog -> simple_results

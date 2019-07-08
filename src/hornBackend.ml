module HornStrategy(I: Z3BasedBackend.OV) = struct
  let ownership theta ovars ocons ff =
    match OwnershipSolver.solve_ownership theta ovars ocons with
    | Some ovals ->
      OwnershipSolver.print_ownership ovals ff
    | None -> raise Z3BasedBackend.OwnershipFailure

  include Z3BasedBackend.StandardSolver(struct
      let strat = "(check-sat-using (then propagate-values qe-light horn))"
    end)
end

module Backend = Z3BasedBackend.Make(HornStrategy)

let solve = Backend.solve

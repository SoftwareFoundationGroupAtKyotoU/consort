module Backend = Z3BasedBackend.Make(struct
  let ownership theta ovars ocons ff =
    match OwnershipSolver.solve_ownership theta ovars ocons with
    | Some ovals ->
      OwnershipSolver.print_ownership ovals ff
    | None -> raise SmtLibBackend.OwnershipFailure

    let z3_tactic = "(check-sat-using (then propagate-values qe-light horn))"
  end)

let solve = Backend.solve

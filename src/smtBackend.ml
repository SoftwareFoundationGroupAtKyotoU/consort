module Backend = Z3BasedBackend.Make(struct
    let ownership _ ovars owner_cons ff =
      OwnershipSolver.print_ownership_constraints ovars owner_cons ff

  
    let z3_tactic = "(check-sat)"
  end)

let solve = Backend.solve

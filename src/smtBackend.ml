module Backend = Z3BasedBackend.Make(struct
    let ownership { Inference.Result.ovars; Inference.Result.ownership = owner_cons; _ } ff =
      OwnershipSolver.print_ownership_constraints ovars owner_cons ff

  
    let z3_tactic = "(check-sat)"
  end)

let solve = Backend.solve

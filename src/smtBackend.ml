module SMTStrategy(I: Z3BasedBackend.OV) = struct    
  let ownership _ ovars owner_cons ff =
    OwnershipSolver.print_ownership_constraints ovars owner_cons ff

  include Z3BasedBackend.StandardSolver(struct
      let strat = "(check-sat)"
    end)
end

module Backend = Z3BasedBackend.Make(SMTStrategy)

let solve = Backend.solve

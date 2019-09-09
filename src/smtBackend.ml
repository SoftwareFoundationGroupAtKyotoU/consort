module Backend = Z3BasedBackend.Make(struct
    let z3_tactic = "(check-sat)"
  end)

let solve = Backend.solve

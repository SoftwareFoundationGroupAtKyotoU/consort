module Backend = functor (O : sig
    val solve_ownership : Inference.Result.t -> (int * float) list option
  end) -> Z3BasedBackend.Make(struct
    let ownership res ff =
      match O.solve_ownership res with
      | Some ovals ->
        OwnershipSolver.print_ownership ovals ff
      | None -> raise SmtLibBackend.OwnershipFailure

    let z3_tactic = "(check-sat-using (then propagate-values qe-light horn))"
  end)

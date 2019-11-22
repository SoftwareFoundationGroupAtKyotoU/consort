module type SOLVER_BACKEND = sig
  val solve: defn_file:(string option) -> Solverlib.SexpPrinter.t -> Solverlib.Solver.result
end

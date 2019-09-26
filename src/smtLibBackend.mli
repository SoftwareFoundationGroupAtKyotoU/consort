module type STRATEGY = sig
  val solve: Solver.solve_fn
end

type intrinsic_interp  = (string StringMap.t) * string option
type solver_intf = (interp:intrinsic_interp -> Inference.Result.t -> Solver.result) Solver.option_fn
module Make(S: STRATEGY) : sig
  val solve : solver_intf
end

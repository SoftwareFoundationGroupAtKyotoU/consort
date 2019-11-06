type intrinsic_interp  = (string StringMap.t) * string option
type solver_intf = (interp:intrinsic_interp -> Inference.Result.t -> Solver.result) Solver.option_fn
module Make(S: Solver.SOLVER_BACKEND) : sig
  val solve :
    interp:string StringMap.t * string option ->
    Inference.Result.t -> Solver.result
end

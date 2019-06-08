module SMTStrategy : Z3BasedBackend.STRATEGY
val solve: debug_cons:bool -> get_model:bool -> interp:(string StringMap.t * string option) -> Inference.Result.t -> bool

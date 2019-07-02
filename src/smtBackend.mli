module SMTStrategy : Z3BasedBackend.STRATEGY
val solve: debug_cons:bool -> ?save_cons:string -> get_model:bool -> interp:(string StringMap.t * string option) -> Inference.Result.t -> bool

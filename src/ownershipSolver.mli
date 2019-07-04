val ovar_name : int -> string
val print_owner_decl : int list -> SexpPrinter.t -> unit
val po : RefinementTypes.ownership -> SexpPrinter.t -> unit
val print_ownership_constraints :
  int list -> Inference.ocon list -> SexpPrinter.t -> unit
val print_ownership :
  (int * float) list -> SexpPrinter.t -> unit
val solve_ownership :
  RefinementTypes.funtype StringMap.t ->
  int list -> Inference.ocon list -> (int * float) list option
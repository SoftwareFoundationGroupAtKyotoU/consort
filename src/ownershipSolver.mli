val ovar_name : int -> string
val print_owner_decl : int list -> SexpPrinter.t -> unit
val po : RefinementTypes.ownership -> (Sexplib.Sexp.t -> 'a) -> 'a
val print_ownership_constraints :
  int list -> Inference.ocon list -> SexpPrinter.t -> unit
val print_ownership :
  (int * float) list -> SexpPrinter.t -> unit

type options
val default : options

val ownership_arg_gen : unit -> (string * Arg.spec * string) list * (?comb:options -> unit -> options)
val solve_ownership :
  opts:options ->
  ?save_cons:string ->
  Inference.Result.t ->
  (int * float) list option

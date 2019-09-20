type ownership =
    OVar of int
  | OConst of float

type ocon =
  (* Constraint ownership variable n to be 1 *)
  | Write of ownership
  (* ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Shuff of (ownership * ownership) * (ownership * ownership)
  | Split of ownership * (ownership * ownership)
  | Eq of ownership * ownership
  (* For well-formedness: if o1 = 0, then o2 = 0 *)
  | Wf of ownership * ownership
  | Ge of ownership * ownership

type options
val default : options

val ownership_arg_gen : unit -> (string * Arg.spec * string) list * (?comb:options -> unit -> options)
val solve_ownership :
  opts:options ->
  ?save_cons:string ->
  (int list * ocon list) ->
  (int * float) list option

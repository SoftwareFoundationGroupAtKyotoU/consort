(** An ownership is either a variable, or a constant (between 0.0 and 1.0, incl) *)
type ownership =
    OVar of int (** A variable with id int *)
  | OConst of float (** a constant ownership with the given rational number *)

type ocon =
  | Live of ownership (** The ownership must be greater than 0 (only emitted in relaxed mode) *)
  | Write of ownership (** Constraint ownership variable n to be 1 *)
  | Shuff of (ownership * ownership) * (ownership * ownership) (** ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Split of ownership * (ownership * ownership) (** Split (o,(s,t)) is the constraint that o = s + t *)
  | Eq of ownership * ownership (** o1 = o2 *)
  | Wf of ownership * ownership (** For well-formedness: if o1 = 0, then o2 = 0 *)
  | Ge of ownership * ownership (** o1 >= o2 *)

val solve_ownership :
  opts:ArgOptions.Solver.options ->
  ?save_cons:string ->
  (int list * ocon list * Std.IntSet.t) ->
  (int * float) list option

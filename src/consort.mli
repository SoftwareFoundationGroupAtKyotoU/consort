module Options :
  sig
    type solver =
      | Hoice
      | Spacer
      | Z3SMT
      | Null

    type t = {
      debug_pred: bool;
      debug_cons: bool;
      debug_ast: bool;
      save_cons: string option;
      annot_infr: bool;
      print_model: bool;
      seq_solver: bool;
      check_trivial: bool;
      dry_run : bool;
      solver: solver;
      solver_opts: Solver.options;
      own_solv_opts: OwnershipSolver.options;
    }

    type arg_spec = (string * Arg.spec * string) list * (?comb:t -> unit -> t)
    val debug_arg_gen : unit -> arg_spec
    val solver_arg_gen : unit -> arg_spec
    val solver_opt_gen : unit -> arg_spec
    val seq : (unit -> arg_spec) -> arg_spec -> arg_spec
    val default : t
  end

type reason =
  | Timeout
  | Unsafe
  | SolverError of string
  | Aliasing

type check_result =
  | Verified
  | Unverified of reason

val result_to_string : check_result -> string
val reason_to_string : reason -> string

val check_file : ?opts:Options.t -> ?intrinsic_defn:Intrinsics.interp_t -> string -> check_result

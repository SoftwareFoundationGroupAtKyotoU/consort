module Options :
  sig
    type t = {
      debug_cons: bool;
      debug_ast: bool;
      save_cons: string option;
      annot_infr: bool;
      print_model: bool;
      dry_run : bool;
      check_trivial: bool;
      solver: ArgOptions.Solver.choice;
      dump_ir : string option;
      relaxed_mode : bool;
      omit_havoc: bool;
      null_checks: bool;
      solver_opts: ArgOptions.Solver.options;
      own_solv_opts: ArgOptions.Solver.options
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
  | UnhandledSolverOutput of string
  | SolverError of string
  | Aliasing
  | Unknown

type check_result =
  | Verified
  | Unverified of reason

val result_to_string : check_result -> string
val reason_to_string : reason -> string

val check_file : ?opts:Options.t -> ?intrinsic_defn:Intrinsics.interp_t -> string -> check_result

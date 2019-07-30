module Options :
  sig
    type t = {
      debug_pred : bool;
      debug_cons : bool;
      debug_ast : bool;
      save_cons : string option;
      annot_infr : bool;
      print_model : bool;
      seq_solver: bool;
      check_trivial: bool;
      dry_run: bool
    }
    type arg_spec = (string * Arg.spec * string) list * (?comb:t -> unit -> t)
    val debug_arg_gen : unit -> arg_spec
    val solver_arg_gen : unit -> arg_spec
    val seq : (unit -> arg_spec) -> arg_spec -> arg_spec
    val default : t
  end
val check_file : ?opts:Options.t -> ?intrinsic_defn:Intrinsics.interp_t -> string -> bool

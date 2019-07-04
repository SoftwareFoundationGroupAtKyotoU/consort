module Options :
  sig
    type t = {
      debug_pred : bool;
      debug_cons : bool;
      debug_ast : bool;
      save_cons : string option;
      annot_infr : bool;
      print_model : bool;
    }
    val get_arg_gen : unit -> (string * Arg.spec * string) list * (unit -> t)
    val default : t
  end
val check_file : ?opts:Options.t -> ?intrinsic_defn:string -> string -> bool

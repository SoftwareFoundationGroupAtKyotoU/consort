module Options :
  sig
    type t = ArgOptions.t

    type arg_spec = (string * Arg.spec * string) list * (?comb:t -> unit -> t)
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

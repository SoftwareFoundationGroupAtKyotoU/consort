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

val check_file : ?opts:ArgOptions.t -> ?intrinsic_defn:Intrinsics.interp_t -> string -> check_result

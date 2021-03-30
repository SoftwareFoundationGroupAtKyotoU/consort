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

val reason_to_string : reason -> bool -> string
val result_to_string : check_result -> string

val check_file : ?opts:ArgOptions.t -> string -> check_result

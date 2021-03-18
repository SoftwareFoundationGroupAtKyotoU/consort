type result = 
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string
  | Error of string
  | Unknown

type cont = Process.t * (unit -> result) * (unit -> unit)

module type SOLVER_BACKEND = sig
  val solve: opts:ArgOptions.t -> SexpPrinter.t -> result
end

let add_extra_arg () cmd_extra =
  match cmd_extra with
  | Some s -> " " ^ s
  | None -> ""

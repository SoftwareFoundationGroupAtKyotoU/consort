type result = 
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string
  | Error of string
  | Unknown

type 'a option_fn = opts:ArgOptions.Solver.options -> debug_cons:bool ->  ?save_cons:string -> get_model:bool -> 'a
type cont = Process.t * (unit -> result) * (unit -> unit)

module type SOLVER_BACKEND = sig
  val solve: defn_file:(string option) -> SexpPrinter.t -> result
end

let add_extra_arg () cmd_extra =
  match cmd_extra with
  | Some s -> " " ^ s
  | None -> ""

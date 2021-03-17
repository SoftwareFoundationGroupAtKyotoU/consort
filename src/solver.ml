type result = 
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string
  | Error of string
  | Unknown

type options = ArgOptions.Solver.options

let default = ArgOptions.Solver.default
type 'a option_fn = opts:options -> debug_cons:bool ->  ?save_cons:string -> get_model:bool -> 'a
type solve_fn = (defn_file:(string option) -> SexpPrinter.t -> result) option_fn   
type cont = Process.t * (unit -> result) * (unit -> unit)

module type SOLVER_BACKEND = sig
  val solve: defn_file:(string option) -> SexpPrinter.t -> result
end

let add_extra_arg () cmd_extra =
  match cmd_extra with
  | Some s -> " " ^ s
  | None -> ""

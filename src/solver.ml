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

let opt_gen ?nm ?(solv_nm="solver") () =
  let open Arg in
  let pref = Option.map (fun s -> s ^ "-") nm |> Option.value ~default:"" in
  let timeout = ref default.timeout in
  let command = ref None in
  let extra = ref None in
  ([
    ("-" ^ pref ^ "timeout", Set_int timeout, Printf.sprintf "Timeout for %s in seconds" solv_nm);
    ("-" ^ pref ^ "command", String (fun s -> command := Some s), Printf.sprintf "Executable for %s" solv_nm);
    ("-" ^ pref ^ "solver-args", String (fun s -> extra := Some s), Printf.sprintf "Extra arguments to pass wholesale to %s" solv_nm)
  ], fun ?comb:_ () ->
      let open ArgOptions.Solver in
     {
       timeout = !timeout;
       command = !command;
       command_extra = !extra
     })

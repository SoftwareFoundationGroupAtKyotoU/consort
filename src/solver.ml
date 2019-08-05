type result = 
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string

type options = {
  timeout : int;
  command : string option;
}

let default = {
  timeout = 30;
  command = None
}

type solve_fn = opts:options -> debug_cons:bool ->  ?save_cons:string -> get_model:bool -> defn_file:(string option) -> SexpPrinter.t -> result

let opt_gen ?nm ?(solv_nm="solver") () =
  let open Arg in
  let pref = Option.map (fun s -> s ^ "-") nm |> Option.value ~default:"" in
  let timeout = ref default.timeout in
  let command = ref None in
  ([
    ("-" ^ pref ^ "timeout", Set_int timeout, Printf.sprintf "Timeout for %s in seconds" solv_nm);
    ("-" ^ pref ^ "command", String (fun s -> command := Some s), Printf.sprintf "Executable for %s" solv_nm)
  ], fun ?comb:_ () ->
     {
       timeout = !timeout;
       command = !command
     })

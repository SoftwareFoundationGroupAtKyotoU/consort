module Solver = struct
  type options = {
    timeout : int;
    command : string option;
    command_extra : string option;
  }

  let default = {
    timeout = 30;
    command = None;
    command_extra = None
  }

  let opt_gen ?nm ?(solv_nm="solver") () =
    let open Arg in
    let pref = Option.map (fun s -> s ^ "-") nm |> Option.value ~default:"" in
    let timeout = ref default.timeout in
    let command = ref None in
    let extra = ref None in
    let spec = [
      ("-" ^ pref ^ "timeout", Set_int timeout,
       Printf.sprintf "Timeout for %s in seconds" solv_nm);
      ("-" ^ pref ^ "command", String (fun s -> command := Some s),
       Printf.sprintf "Executable for %s" solv_nm);
      ("-" ^ pref ^ "solver-args", String (fun s -> extra := Some s),
       Printf.sprintf "Extra arguments to pass wholesale to %s" solv_nm)
    ] in
    let update ?(comb=default) () =
      let _ = comb in {
        timeout = !timeout;
        command = !command;
        command_extra = !extra
      } in
    (spec, update)
end

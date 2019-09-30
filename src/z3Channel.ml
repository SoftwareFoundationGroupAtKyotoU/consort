module Ch = SolverBridge.Make(struct
    type st = Process.t
    let name = "z3"
    let spawn i = i
    open Solver
    let prepare_out ~solver_opts:{ command; timeout; command_extra } save_cons =
      let base_command = Printf.sprintf "%s -in -T:%d%a 2>&1"
          (Option.value ~default:"z3" command)
          timeout
          add_extra_arg command_extra
      in
      let cmd = 
        match save_cons with
        | Some f_name -> Printf.sprintf "tee %s | %s" f_name base_command
        | None -> base_command
      in
      let proc = Process.spawn cmd in
      (proc,proc.Process.proc_stdin)
    let dispose _ = ()
  end)
    
(* remove one of these *)
let call_z3_raw = Ch.call
let call_z3 = Ch.call


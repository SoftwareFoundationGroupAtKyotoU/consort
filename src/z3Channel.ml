module Ch = SolverBridge.Make(struct
    type st = in_channel
    let name = "z3"
    let spawn i = i
    let prepare_out ~timeout ~command save_cons =
      let base_command = Printf.sprintf "%s -in -T:%d"
          (Option.value ~default:"z3" command)
          timeout
      in
      let cmd = 
        match save_cons with
        | Some f_name -> Printf.sprintf "tee %s | %s" f_name base_command
        | None -> base_command
      in Unix.open_process cmd
    let dispose _ = ()
  end)
    
(* remove one of these *)
let call_z3_raw = Ch.call
let call_z3 = Ch.call


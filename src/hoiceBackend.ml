module Ch = SolverBridge.Make(struct
    let name = "hoice"
    type st = (string * string)
    open Solver
    let prepare_out ~solver_opts:{ timeout; command; command_extra} save_cons =
      let (nm,chan) =
        match save_cons with
        | Some s -> (s,open_out s)
        | None ->
          let (nm,chan) = Filename.open_temp_file "HoiceCons" ".smt" in
          at_exit (fun () ->
            Sys.remove nm);
          (nm,chan)
      in
      let base_command = Printf.sprintf "%s -t %d %a"
          (Option.value ~default:"hoice" command)
          timeout
          add_extra_arg command_extra
      in
      (base_command,nm),chan

    let spawn (base_command,nm) =
      Unix.open_process_in @@ Printf.sprintf "%s %s" base_command @@ Filename.quote nm

    let dispose _ = ()
  end)

module Backend = SmtLibBackend.Make(struct
    let solve = Ch.call ~strat:"(check-sat)"
  end)

let solve = Backend.solve

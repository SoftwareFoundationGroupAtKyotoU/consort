module Ch = SolverBridge.Make(struct
    let name = "hoice"
    type st = (string * string)

    let prepare_out ~timeout ~command save_cons =
      let (nm,chan) =
        match save_cons with
        | Some s -> (s,open_out s)
        | None ->
          let (nm,chan) = Filename.open_temp_file "HoiceCons" ".smt" in
          at_exit (fun () ->
            Sys.remove nm);
          (nm,chan)
      in
      let base_command = Printf.sprintf "%s -t %d"
          (Std.Option.value ~default:"hoice" command)
          timeout
      in
      (base_command,nm),chan

    let spawn (base_command,nm) =
      Unix.open_process_in @@ Printf.sprintf "%s %s" base_command @@ Filename.quote nm

    let dispose _ = ()
  end)

module Backend = SmtLibBackend.Make(struct
    let ownership _ _ = ()

    let rec interp_ante =
      let open Inference in
      let open RefinementTypes in
      function
      | ORel (OConst f1,rel,f2) -> begin
          match rel with
          | `Eq -> f1 = f2
          | `Ge -> f1 >= f2
          | `Gt -> f1 > f2
        end
      | ORel (OVar _,_,_) -> failwith "Free ownership variable! Are you using sequential solving?"
      | OAny ol -> List.exists interp_ante ol

    let ownership_ante f =
      let open SexpPrinter in
      if interp_ante f then
        pl "true"
      else
        pl "false"

    let solve = Ch.call ~strat:"(check-sat)"
  end)

let solve = Backend.solve

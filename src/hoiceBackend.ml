module Ch = SolverBridge.Make(struct
    let name = "hoice"
    let base_command = "/home/jtoman/sources/hoice/target/release/hoice -t 30"

    type st = string

    let prepare_out save_cons =
      match save_cons with
      | Some s -> (s,open_out s)
      | None ->
        let (nm,chan) = Filename.open_temp_file "HoiceCons" ".smt" in
        at_exit (fun () ->
          Sys.remove nm);
        (nm,chan)

    let spawn nm =
      Unix.open_process_in @@ Printf.sprintf "%s %s" base_command @@ Filename.quote nm

    let dispose _ = ()
  end)

module Backend = SmtLibBackend.Make(struct
    let ownership _ _ _ _ = ()

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

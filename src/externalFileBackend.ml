module Make(D: sig
      val name : string
      val spawn : command:string option -> timeout:int -> string
      val strat : string
    end) = struct
  module Ch = SolverBridge.Make(struct
      type st = string * string
      let dispose _ = ()
      open Solver
      let prepare_out ~opts =
        let (nm,chan) = Filename.open_temp_file (D.name ^ "Cons") ".smt" in
        at_exit (fun () ->
            Sys.remove nm);
        let base_command =
          let open ArgOptions in
          Printf.sprintf "%s %a"
            (D.spawn ~command:opts.command ~timeout:opts.timeout)
            add_extra_arg opts.command_extra
        in
        (base_command,nm),chan

      let spawn (base_command,nm) =
        let to_ret = Process.spawn @@ Printf.sprintf "%s %s" base_command @@ Filename.quote nm in
        close_out to_ret.Process.proc_stdin;
        to_ret

      let name = D.name
    end)

  let solve = Ch.call ~strat:D.strat
  let solve_cont = Ch.call_cont ~strat:D.strat
end

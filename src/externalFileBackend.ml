module Make(D: sig
      val name : string
      val spawn : command:string option -> timeout:int -> string
      val strat : string
    end) = struct
  module Ch = SolverBridge.Make(struct
      type st = string * string
      let dispose _ = ()
      open Solver
      let prepare_out ~solver_opts:{ timeout; command; command_extra} save_cons =
        let (nm,chan) =
          match save_cons with
          | Some s -> (s,open_out s)
          | None ->
            let (nm,chan) = Filename.open_temp_file (D.name ^ "Cons") ".smt" in
            at_exit (fun () ->
              Sys.remove nm);
            (nm,chan)
        in
        let base_command =
          Printf.sprintf "%s %a"
            (D.spawn ~command ~timeout)
            add_extra_arg command_extra
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

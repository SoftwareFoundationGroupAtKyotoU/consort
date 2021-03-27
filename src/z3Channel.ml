module Ch = SolverBridge.Make(struct
    type st = Process.t
    let name = "z3"
    let spawn i = i
    let prepare_out ~opts =
      let cmd =
        let open Solver in
        let open ArgOptions in
        Printf.sprintf "%s -in -T:%d%a 2>&1"
          (Option.value ~default:"z3" opts.command)
          opts.timeout
          add_extra_arg opts.command_extra in
      let proc = Process.spawn cmd in
      (proc,proc.Process.proc_stdin)
    let dispose _ = ()
  end)

(* remove one of these *)
let call_z3_raw = Ch.call
let call_z3 = Ch.call

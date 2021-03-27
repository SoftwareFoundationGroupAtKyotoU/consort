let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

module type S = sig
  val call :
    opts:ArgOptions.t ->
    strat:string ->
    SexpPrinter.t ->
    Solver.result
  val call_cont :
    opts:ArgOptions.t ->
    strat:string ->
    SexpPrinter.t ->
    Solver.cont
end

module Make(D: sig
      type st
      val spawn : st -> Process.t
      val prepare_out : opts:ArgOptions.t -> st * out_channel
      val dispose : st -> unit
      val name : string
    end) : S = struct
  let _ = D.name

  let handle_return ~opts s p =
    let res = String.trim @@ input_line p.Process.proc_stdout in
    let return_and_close f = Process.dispose p; D.dispose s; f in
    match res with
    | "sat" ->
      let m =
        if opts.ArgOptions.show_model then
          Some (Files.string_of_channel p.Process.proc_stdout)
        else
          None in
      return_and_close @@ Solver.Sat m
    | "unsat" -> return_and_close Solver.Unsat
    | "timeout" -> return_and_close Solver.Timeout
    | "unknown" -> return_and_close Solver.Unknown
    | s ->
      try
        let module SS = Sexplib.Sexp in
        let result_sexp = SS.of_string s in
        match result_sexp with
        | SS.List [ SS.Atom "error"; SS.Atom msg ] ->
          return_and_close @@ Solver.Error msg
        | _ -> return_and_close @@ Solver.Unhandled s
      with
      | Failure _ -> return_and_close @@ Solver.Unhandled s

  let prepare_call ~opts ~strat cons =
    let defn_file = (ArgOptions.get_intr opts).def_file in
    let (s,o) = D.prepare_out ~opts in
    output_string o @@ load_defn defn_file;
    SexpPrinter.to_channel cons o;
    let cmd = "\n" ^ strat ^ "\n" ^ (
        if opts.show_model then "(get-model)\n" else "") in
    output_string o cmd;
    close_out o;
    let p = D.spawn s in
    (s,p)

  let call ~opts ~strat cons =
    let (s,p) = prepare_call ~opts ~strat cons in
    handle_return ~opts s p

  let call_cont ~opts ~strat cons =
    let (s,p) = prepare_call ~opts ~strat cons in
    (p, (fun () -> handle_return ~opts s p), (fun () -> D.dispose s))
end

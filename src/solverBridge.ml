let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

module type S = sig
  val call : (defn_file:string option -> strat:string -> SexpPrinter.t -> Solver.result) Solver.option_fn
  val call_cont : 
    opts:Solver.options ->
    get_model:bool ->
    defn_file:string option ->
    strat:string ->
    SexpPrinter.t ->
    Solver.cont
end

module Make(D: sig
      type st
      val spawn : st -> Process.t
      val prepare_out : solver_opts:Solver.options -> string option -> st * out_channel
      val dispose : st -> unit
      val name : string
    end) : S = struct
  let handle_return get_model s p = 
    let res = String.trim @@ input_line p.Process.proc_stdout in
    let return_and_close f = Process.dispose p; D.dispose s; f in
    match res with
    | "sat" ->
      let m =
        if get_model then
          let model = Files.string_of_channel p.Process.proc_stdout in
          Some model
        else
          None
      in
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

  let prepare_call ~opts ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
    if debug_cons then begin
      let cons_string = (load_defn defn_file) ^ (SexpPrinter.to_string cons) in
      Printf.fprintf stderr "Sending constraints >>>\n%s\n<<<<\nto %s\n" cons_string D.name;
      flush stderr
    end;
    let (s,o) = D.prepare_out ~solver_opts:opts save_cons in
    output_string o @@ load_defn defn_file;
    SexpPrinter.to_channel cons o;
    let cmd = "\n" ^ strat ^ "\n" ^ (
        if get_model then
          "(get-model)\n"
        else
          ""
      )
    in
    output_string o cmd;
    close_out o;
    let p = D.spawn s in
    (s,p)
    
  let call ~opts ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
    let (s,p) = prepare_call ~opts ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons in
    handle_return get_model s p

  let call_cont ~opts ~get_model ~defn_file ~strat cons =
    let (s,p) = prepare_call ~opts ~debug_cons:false ?save_cons:None ~get_model ~defn_file ~strat cons in
    (p, (fun () -> handle_return get_model s p), (fun () -> D.dispose s))
end

let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

module Make(D: sig
      type st
      val spawn : st -> in_channel
      val prepare_out : timeout:int -> command:(string option) -> string option -> st * out_channel
      val dispose : st -> unit
      val name : string
    end) = struct
  let call ~opts ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
    if debug_cons then begin
      let cons_string = (load_defn defn_file) ^ (SexpPrinter.to_string cons) in
      Printf.fprintf stderr "Sending constraints >>>\n%s\n<<<<\nto %s\n" cons_string D.name;
      flush stderr
    end;
    let (s,o) = D.prepare_out ~timeout:opts.Solver.timeout ~command:opts.Solver.command save_cons in
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
    let i = D.spawn s in
    let res = input_line i in
    let return_and_close f = close_in i; D.dispose s; f in
    match res with
    | "sat" ->
      let m =
        if get_model then
          let model = Files.string_of_channel i in
          Some model
        else
          None
      in
      return_and_close @@ Solver.Sat m
    | "unsat" -> return_and_close Solver.Unsat
    | "timeout" -> return_and_close Solver.Timeout
    | s -> return_and_close @@ Solver.Unhandled s
end

module type CONFIG = sig
  val base_command : string
  val name : string
end

let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

module Make(C: CONFIG) = struct
  let call ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =     
    if debug_cons then begin
      let cons_string = (load_defn defn_file) ^ (SexpPrinter.to_string cons) in
      Printf.fprintf stderr "Sending constraints >>>\n%s\n<<<<\nto %s\n" cons_string C.name;
      flush stderr
    end;
    let (i,o) =
      let cmd = 
        match save_cons with
        | Some f_name -> Printf.sprintf "tee %s | %s" f_name C.base_command
        | None -> C.base_command
      in Unix.open_process cmd
    in
    output_string o @@ load_defn defn_file;
    SexpPrinter.to_channel cons o;
    output_string o @@ "\n" ^ strat ^ "\n";
    begin
      if get_model then
        output_string o "(get-model)\n"
      else ()
    end;
    close_out o;
    let res = input_line i in
    let return_and_close f = close_in i; f in
    match res with
    | "sat" ->
      let m =
        if get_model then
          let model = Files.string_of_channel i in
          Some model
        else
          None
      in
      return_and_close @@ Prover.Sat m
    | "unsat" -> return_and_close Prover.Unsat
    | "timeout" -> return_and_close Prover.Timeout
    | s -> return_and_close @@ Prover.Unhandled s

end
    

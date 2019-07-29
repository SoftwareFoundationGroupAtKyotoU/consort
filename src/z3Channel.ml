let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

let base_command = "z3 -in -T:30"

type solver_res =
  | Unsat
  | Sat of string option
  | Timeout
  | Unhandled of string
  
let call_z3_raw ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
  if debug_cons then begin
    let cons_string = (load_defn defn_file) ^ (SexpPrinter.to_string cons) in
    Printf.fprintf stderr "Sending constraints >>>\n%s\n<<<<\nto z3\n" cons_string;
    flush stderr
  end;
  let (i,o) =
    let cmd = 
      match save_cons with
      | Some f_name -> Printf.sprintf "tee %s | %s" f_name base_command
      | None -> base_command
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
    return_and_close @@ Sat m
  | "unsat" -> return_and_close Unsat
  | "timeout" -> return_and_close Timeout
  | s -> return_and_close @@ Unhandled s

let call_z3 ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
  call_z3_raw ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons


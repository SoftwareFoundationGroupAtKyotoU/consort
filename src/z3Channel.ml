let load_defn = function
  | Some f -> Files.string_of_file f
  | None -> ""

let base_command = "z3 -in -T:30"

let call_z3_raw ~debug_cons ?save_cons ~defn_file ~strat cons =
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
  output_string o "(get-model)\n";
  close_out o;
  let res = input_line i in
  if res = "sat" then
    let model = Files.string_of_channel i in
    close_in i;
    (res,Some model)
  else
    (res,None)

let call_z3 ~debug_cons ?save_cons ~get_model ~defn_file ~strat cons =
  let (res,m) = call_z3_raw ~debug_cons ?save_cons ~defn_file ~strat cons in
  if get_model then begin
    match m with
    | Some m -> prerr_endline m; flush stderr
    | None -> ()
  end;
  res = "sat"


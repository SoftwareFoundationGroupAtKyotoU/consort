let check_file ?(print_pred=false) ?(print_cons=false) ?(print_ast=false) in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  let ast = try
    Parser.prog Lexer.read lexbuf
  with
      Parser.Error -> let open Lexing in
        failwith @@ Printf.sprintf "Parse error on line %d, col: %d" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)
  in
  let program_types = SimpleChecker.typecheck_prog ast in
  if print_ast then begin
    print_endline @@ Ast.pretty_print_program ast;
    let open SimpleChecker in
    StringMap.iter (fun n a ->
      Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
    ) program_types
  end;
  let (o, ov, r, a) = RefinementTypes.infer ~print_pred program_types ast in
  Z3Backend.solve ~print_cons o ov r a

let check_file ?(print_ast=false) in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  let ast = try
    Parser.prog Lexer.read lexbuf
  with
      Parser.Error -> let open Lexing in
        failwith @@ Printf.sprintf "Parse error on line %d, col: %d" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol)
  in
  if print_ast then
    print_endline @@ Ast.pretty_print_program ast;
  let open SimpleChecker in
  let program_types = typecheck_prog ast in
  StringMap.iter (fun n a ->
    Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
  ) program_types;
  let (o, ov, r, a) = RefinementTypes.infer program_types ast in
  Z3Backend.solve o ov r a

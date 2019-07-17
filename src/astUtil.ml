let parse_file in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  try
    Parser.prog Lexer.read lexbuf |> SurfaceAst.simplify
  with
    | Parser.Error -> let open Lexing in
    failwith @@ Printf.sprintf "Parse error on line %d, col: %d in file %s" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in_name
    | Failure _ ->
      let open Lexing in
      failwith @@ Printf.sprintf "Lexing error on line %d, col: %d in file %s" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in_name


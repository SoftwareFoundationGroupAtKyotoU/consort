let parse_file in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  Locations.set_file_name lexbuf in_name 1;
  try
    Parser.prog Lexer.read lexbuf |> SurfaceAst.simplify
  with
    | Parser.Error -> let open Lexing in
    failwith @@ Printf.sprintf "Parse error at %s" @@ Locations.string_of_location lexbuf.lex_start_p
    | Failure _ ->
      let open Lexing in
      failwith @@ Printf.sprintf "Lexing error at %s" @@ Locations.string_of_location lexbuf.lex_curr_p


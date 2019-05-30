let () =
  let in_name = Sys.argv.(1) in
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in

  let ast = Parser.prog Lexer.read lexbuf in
  print_endline @@ Ast.pretty_print_program ast;
  let open SimpleChecker in
  let program_types = typecheck_prog ast in
  StringMap.iter (fun n a ->
    Printf.printf "%s: %s\n" n @@ fntype_to_string a
  ) program_types

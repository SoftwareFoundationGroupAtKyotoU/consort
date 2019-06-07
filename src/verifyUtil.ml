let check_file ?(print_pred=false) ?(print_cons=false) ?(print_ast=false) ?(get_model=false) ?intrinsic_defn in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  let ast = try
    Parser.prog Lexer.read lexbuf |> SurfaceAst.simplify
  with
      Parser.Error -> let open Lexing in
        failwith @@ Printf.sprintf "Parse error on line %d, col: %d in file %s" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in_name
  in
  let intr = match intrinsic_defn with
    | Some i_name -> Intrinsics.load i_name
    | None -> Intrinsics.empty
  in
  let simple_typing = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let program_types = SimpleChecker.typecheck_prog simple_typing ast in
  if print_ast then begin
    print_endline @@ Ast.pretty_print_program ast;
    StringMap.iter (fun n a ->
      Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
    ) program_types
  end;
  let (o, ov, r, a) = Inference.infer ~print_pred ~intrinsics:intr.Intrinsics.op_interp program_types ast in
  Z3Backend.solve ~print_cons ~get_model ~interp:(intr.Intrinsics.rel_interp,intr.Intrinsics.def_file) o ov r a

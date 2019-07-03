let pprint_ty_env =
  let open PrettyPrint in
  fun ty_envs i ->
    let ty_env = Hashtbl.find ty_envs i in
    if (StringMap.cardinal ty_env) = 0 then
      pl [ ps "/* empty */"; newline ]
    else
      let pp_ty_env = StringMap.bindings ty_env
        |> List.map (fun (k,t) ->
            pb [
              pf "%s: " k;
              RefinementTypes.pp_type t
            ]
          )
        |> psep_gen newline
      in
      pl [
        indent_from_here;
        ps "/*"; newline;
        pp_ty_env; dedent; newline;
        ps "*/"; newline
      ]

let check_file ?(print_pred=false) ?(print_cons=false) ?save_cons ?(print_ast=false) ?(annot_infr=false) ?(get_model=false) ?intrinsic_defn in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  let ast = try
    Parser.prog Lexer.read lexbuf |> SurfaceAst.simplify
  with
    | Parser.Error -> let open Lexing in
    failwith @@ Printf.sprintf "Parse error on line %d, col: %d in file %s" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in_name
    | Failure _ ->
      let open Lexing in
      failwith @@ Printf.sprintf "Lexing error on line %d, col: %d in file %s" lexbuf.lex_curr_p.pos_lnum (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol) in_name
  in
  let intr = match intrinsic_defn with
    | Some i_name -> Intrinsics.load i_name
    | None -> Intrinsics.empty
  in
  let simple_typing = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let program_types = SimpleChecker.typecheck_prog simple_typing ast in
  if print_ast then begin
    print_endline @@ AstPrinter.pretty_print_program ast;
    StringMap.iter (fun n a ->
      Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
    ) program_types
  end;
  let r = Inference.infer ~print_pred ~save_types:annot_infr ~intrinsics:intr.Intrinsics.op_interp program_types ast in
  if annot_infr then begin
    let ty_envs = r.Inference.Result.ty_envs in
    print_endline @@ AstPrinter.pretty_print_program ~with_labels:false ~annot:(pprint_ty_env ty_envs) ast
  end;
  HornBackend.solve ~debug_cons:print_cons ?save_cons ~get_model ~interp:(intr.Intrinsics.rel_interp,intr.Intrinsics.def_file) r

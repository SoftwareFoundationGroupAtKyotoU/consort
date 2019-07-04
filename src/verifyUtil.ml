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

module Options = struct
  type t = {
    debug_pred: bool;
    debug_cons: bool;
    debug_ast: bool;
    save_cons: string option;
    annot_infr: bool;
    print_model: bool
  }

  let get_arg_gen () =
    let open Arg in
    let debug_cons = ref true in
    let debug_pred = ref true in
    let debug_ast = ref true in
    let show_model = ref false in
    let annot_infr = ref false in
    let save_cons = ref None in
    let all_debug_flags = [ debug_cons; debug_pred; debug_ast; show_model ] in
    let mk_arg key flg what =
      [
        ("-no-" ^ key, Clear flg, Printf.sprintf "Do not print %s" what);
        ("-show-" ^key, Set flg, Printf.sprintf "Print %s on stderr" what)
      ] in
    let arg_defs =
      (mk_arg "cons" debug_cons "constraints sent to Z3") @
        (mk_arg "ast" debug_ast "(low-level) AST") @
        (mk_arg "pred" debug_pred "predicate explanations") @
        (mk_arg "model" show_model "inferred model") @
        [
          ("-annot-infr", Set annot_infr, "Annotate the program with the inferred types");
          ("-show-model", Set show_model, "Print model produced from successful verification");
          ("-save-cons", String (fun r -> save_cons := Some r), "Save constraints in <file>");
          ("-show-all", Unit (fun () ->
             List.iter (fun r -> r := true) all_debug_flags
           ), "Show all debug output");
          ("-none", Unit (fun () ->
             List.iter (fun r -> r:= false) all_debug_flags
           ), "Suppress all debug output")
        ] in
    (arg_defs, (fun () ->
       {
         debug_pred = !debug_pred;
         debug_ast = !debug_ast;
         print_model = !show_model;
         annot_infr = !annot_infr;
         debug_cons = !debug_cons;
         save_cons = !save_cons
       }))

  let default = {
    debug_pred = false;
    debug_cons = false;
    save_cons = None;
    debug_ast = false;
    annot_infr = false;
    print_model = false
  }
end


let check_file ?(opts=Options.default) ?intrinsic_defn in_name =
  let open Options in
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
  if opts.debug_ast then begin
    print_endline @@ AstPrinter.pretty_print_program ast;
    StringMap.iter (fun n a ->
      Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
    ) program_types
  end;
  let r = Inference.infer ~print_pred:opts.debug_pred ~save_types:opts.annot_infr ~intrinsics:intr.Intrinsics.op_interp program_types ast in
  if opts.annot_infr then begin
    let ty_envs = r.Inference.Result.ty_envs in
    print_endline @@ AstPrinter.pretty_print_program ~with_labels:false ~annot:(pprint_ty_env ty_envs) ast
  end;
  HornBackend.solve
    ~debug_cons:opts.debug_cons
    ?save_cons:opts.save_cons
    ~get_model:opts.print_model
    ~interp:(intr.Intrinsics.rel_interp,intr.Intrinsics.def_file) r

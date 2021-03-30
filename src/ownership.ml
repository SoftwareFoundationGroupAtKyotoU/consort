let print_program ~o_map ~o_printer r ast =
  let open PrettyPrint in
  let open OwnershipInference.Result in
  let rec print_type =
    let open OwnershipInference in
    function
    | Int ->
      ps "int"
    | Tuple tl ->
      pl [
        ps "(";
        psep_gen (pf ",@ ") @@ List.map print_type tl;
        ps ")"
      ]
    | Ref (t,o) ->
      pf "%a@ ref@ %a"
        (ul print_type) t
        (ul o_printer) (o_map o)
    | Array (t,o) ->
      pf "[%a]@ %a"
        (ul print_type) t
        (ul o_printer) (o_map o)
    | Mu (id,t) ->
      pf "%s '%d.@ %a"
        Greek.mu
        id
        (ul print_type) t
    | TVar id ->
      pf "'%d" id
  in
  let print_type_binding (k, t) = pb [pf "%s: " k; print_type t] in
  let print_type_sep t = List.map print_type t |> psep_gen (pf ",@ ") in
  let pp_ty_env (i, _) _ =
    let ty_env = Std.IntMap.find i r.ty_envs in
    let pp_env =
      StringMap.bindings ty_env
      |> List.map print_type_binding
      |> psep_gen newline in
    if (StringMap.cardinal ty_env) = 0 then
      pl [ps "/* empty */"; newline]
    else
      pblock ~nl:true ~op:(ps "/*") ~body:pp_env ~close:(ps "*/")
  in
  let pp_f_type f =
    let theta = StringMap.find f r.theta in
    pl [
      pb [
        ps "/* ("; print_type_sep theta.arg_types; ps ")";
        pf "@ ->@ ";
        ps "(";
        print_type_sep theta.output_types;
        pf "@ |@ ";
        print_type theta.result_type;
        ps ") */";
      ];
      newline
    ]
  in
  AstPrinter.pretty_print_program ~annot:pp_ty_env ~annot_fn:pp_f_type stdout ast

let pp_owner =
  let open OwnershipInference in
  let open PrettyPrint in
  function
  | OConst o -> pf "%f" o
  | OVar v -> pf "$%d" v

let ownership_infr ~opts file =
  let ast = AstUtil.parse_file file in
  let simple_op = RefinementTypes.to_simple_funenv (ArgOptions.get_intr opts).op_interp in
  let ((_,SimpleChecker.SideAnalysis.{ fold_locs = fl; _ }) as simple_res) = SimpleChecker.typecheck_prog simple_op ast in
  print_endline "FOLD LOCATIONS>>>";
  Std.IntSet.iter (Printf.printf "* %d\n") fl;
  print_endline "<<";
  let r = OwnershipInference.infer ~opts simple_res ast in
  print_program ~o_map:(fun o -> o) ~o_printer:pp_owner r ast;
  let open PrettyPrint in
  let o_solve = OwnershipSolver.solve_ownership ~opts r in
  match o_solve with
  | None -> print_endline "Could not solve ownership constraints"
  | Some soln ->
    print_program ~o_map:(fun o ->
        match o with
        | OConst o -> o
        | OVar o -> List.assoc o soln
      ) ~o_printer:(pf "%f") r ast

let () =
  let n = ref None in
  let opts = ArgOptions.parse (fun s -> n := Some s) "Run ownership inference on <file>" in
  match !n with
  | None -> print_endline "No file provided"
  | Some f -> ownership_infr ~opts f

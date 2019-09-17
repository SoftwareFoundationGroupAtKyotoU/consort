let print_program ~o_map ~o_printer r ast =
  let open PrettyPrint in
  let open OwnershipInference in
  let rec print_type = function
    | Int -> ps "int"
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
    | TVar id -> pf "'%d" id
  in
  let print_type_binding (k,t) =
    let open PrettyPrint in
    pb [
      pf "%s: " k;
      print_type t
    ]
  in
  let pp_ty_env (i,_) _ =
    let ty_env = Std.IntMap.find i r.Result.ty_envs in
    if (StringMap.cardinal ty_env) = 0 then
      pl [ ps "/* empty */"; newline ]
    else
      let pp_env = StringMap.bindings ty_env
        |> List.map print_type_binding
        |> psep_gen newline
      in
      pblock ~nl:true ~op:(ps "/*") ~body:pp_env ~close:(ps "*/")
  in
  let pp_f_type f =
    let open RefinementTypes in
    let { arg_types; output_types; result_type } = StringMap.find f r.Result.theta in
    let in_types =
      List.map print_type arg_types
      |> psep_gen (pf ",@ ")
    in
    let out_types =
      List.map print_type output_types
      |> psep_gen (pf ",@ ")
    in
    pl [
      pb [
        ps "/* ("; in_types; ps ")";
        pf "@ ->@ ";
        ps "("; out_types; pf "@ |@ "; print_type result_type; ps ") */";
      ];
      newline
    ]
  in
  AstPrinter.pretty_print_program ~annot:pp_ty_env ~annot_fn:pp_f_type stdout ast

let pp_owner =
  let open OwnershipSolver in
  let open PrettyPrint in
  function
  | OConst o -> pf "%f" o
  | OVar v -> pf "$%d" v

let ownership_infr debug i_gen o_gen file =
  let intr = i_gen () in
  let ast = AstUtil.parse_file file in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let ((_,SimpleChecker.SideAnalysis.{ fold_locs = fl; _ }) as simple_res) = SimpleChecker.typecheck_prog simple_op ast in
  print_endline "FOLD LOCATIONS>>>";
  Std.IntSet.iter (Printf.printf "* %d\n") fl;
  print_endline "<<";
  let r = OwnershipInference.infer simple_res intr.Intrinsics.op_interp ast in
  print_program ~o_map:(fun o -> o) ~o_printer:pp_owner r ast;
  let open PrettyPrint in
  let o_solve = OwnershipSolver.solve_ownership ~opts:(o_gen ()) ?save_cons:!debug (r.OwnershipInference.Result.ovars,r.OwnershipInference.Result.ocons) in
  match o_solve with
  | None -> print_endline "Could not solve ownership constraints"
  | Some soln ->
    print_program ~o_map:(fun o ->
        match o with
        | OwnershipSolver.OConst o -> o
        | OwnershipSolver.OVar o -> List.assoc o soln
      ) ~o_printer:(pf "%f") r ast

let () =
  let (i_list, gen) = Intrinsics.option_loader () in
  let (o_list, o_gen) = OwnershipSolver.ownership_arg_gen () in
  let debug = ref None in
  let spec = ("-save-cons", Arg.String (fun s -> debug := Some s), "Save constraints to <file>") :: (i_list @ o_list) in
  Files.run_with_file spec "Run ownership inference on <file>" @@ ownership_infr debug gen o_gen

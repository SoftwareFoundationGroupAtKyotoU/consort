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

let print_fold_locations simple_res =
  let open SimpleChecker.SideAnalysis in
  let _, side = simple_res in
  print_endline "FOLD LOCATIONS >>>";
  Std.IntSet.iter (Printf.printf "* %d\n") side.fold_locs;
  print_endline "<<<"

let print_inference infer_res ast =
  let open PrettyPrint in
  let open OwnershipInference in
  let o_map o = o in
  let o_printer = function
    | OConst o -> pf "%f" o
    | OVar v -> pf "$%d" v in
  print_program ~o_map ~o_printer infer_res ast

let print_ownership ownership_res infer_res ast =
  let open PrettyPrint in
  let open OwnershipInference in
  match ownership_res with
  | None -> print_endline "Could not solve ownership constraints"
  | Some o_res ->
    let o_map = function
      | OConst o -> o
      | OVar o -> List.assoc o o_res in
    let o_printer = pf "%f" in
    print_program ~o_map ~o_printer infer_res ast

let ownership_infr ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_op = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_op ast in
  print_fold_locations simple_res;
  let infer_res = OwnershipInference.infer ~opts simple_res ast in
  print_inference infer_res ast;
  let ownership_res = OwnershipSolver.solve_ownership ~opts infer_res in
  print_ownership ownership_res infer_res ast;
  let open Consort in
  match ownership_res with
  | None -> Unverified Aliasing
  | Some _ -> Verified

let () =
  let n = ref None in
  let opts = ArgOptions.parse (fun s -> n := Some s) "Run ownership inference on <file>" in
  match !n with
  | None -> print_endline "No file provided"
  | Some f -> let _ = ownership_infr ~opts f in ()

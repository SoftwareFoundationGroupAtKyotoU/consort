type reason =
  | Timeout
  | Unsafe
  | UnhandledSolverOutput of string
  | SolverError of string
  | Aliasing
  | Unknown

type check_result =
  | Verified
  | Unverified of reason

let reason_to_string reason with_msg =
  match reason with
  | Timeout -> "timeout"
  | Unsafe -> "unsafe"
  | UnhandledSolverOutput s ->
    if with_msg then
      Printf.sprintf "unhandled solver output: \"%s\"" s
    else "unhandled"
  | SolverError s ->
    if with_msg then
      Printf.sprintf "solver: \"%s\"" s
    else "solver-error"
  | Aliasing -> "ownership"
  | Unknown -> "unknown"

let result_to_string = function
  | Verified -> "VERIFIED"
  | Unverified r -> Printf.sprintf "UNVERIFIED (%s)" @@ reason_to_string r true

let solver_result_to_check_result =
  let open Solver in
  function
  | Unsat -> Unverified Unsafe
  | Sat _ -> Verified
  | Timeout -> Unverified Timeout
  | Unhandled msg -> Unverified (UnhandledSolverOutput msg)
  | Error msg -> Unverified (SolverError msg)
  | Unknown -> Unverified Unknown

let choose_solver =
  let open ArgOptions.Solver in
  function
  | Eldarica -> EldaricaBackend.solve
  | Hoice -> HoiceBackend.solve
  | Null -> NullSolver.solve
  | Parallel -> ParallelBackend.solve
  | Spacer -> HornBackend.solve
  | Z3SMT -> SmtBackend.solve

let pcomment ~body =
  let open PrettyPrint in
  pblock ~nl:true ~op:(ps "/*") ~body ~close:(ps "*/")

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
    if (StringMap.cardinal ty_env) = 0 then
      pl [ps "/* empty */"; newline]
    else
      let pp_env =
        StringMap.bindings ty_env
        |> List.map print_type_binding
        |> psep_gen newline in
      pcomment ~body:pp_env
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

let print_typecheck (f_types, side) ast =
  let open Ast in
  let open PrettyPrint in
  let open SimpleChecker.SideAnalysis in
  let open SimpleTypes in
  let annot_fn f_name =
    let s = fntype_to_string @@ StringMap.find f_name f_types in
    pl [pf "/* %s */" s; newline] in
  let from_ty_patt ty patt =
    let rec patt_loop acc p t =
      match p, t with
      | PVar v, _ -> (pf "%s: %s" v @@ type_to_string t)::acc
      | PNone, _ -> acc
      | PTuple pl, `Tuple tl -> List.fold_left2 patt_loop acc pl tl
      | _, _ -> assert false in
    let ty_list = patt_loop [] patt ty |> List.rev in
    match List.length ty_list with
    | 0 -> pl [ps "/* (no bindings) */"; newline]
    | 1 -> pl [ps "/* "; pl ty_list; ps " */"; newline]
    | _ -> pcomment ~body:(psep_gen newline ty_list) in
  let annot (id, _) e =
    match Std.IntMap.find_opt id side.let_types, e with
    | Some ty, Let (patt, _, _) -> from_ty_patt ty patt
    | _ -> null in
  AstPrinter.pretty_print_program ~annot_fn ~annot stdout ast

let to_hint o_res record =
  let open OwnershipInference in
  let o_map = function
    | OVar v -> List.assoc v o_res
    | OConst c -> c in
  let s_map (a, b) = o_map a, o_map b in
  {
    splits = SplitMap.map s_map record.splits;
    gen = GenMap.map o_map record.gen
  }

let get_solve ~opts =
  let open ArgOptions in
  let module Backend = struct
    let solve = choose_solver opts.solver
  end in
  let module S = FlowBackend.Make(Backend) in
  S.solve

let consort ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_typing = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_typing ast in
  let infer_res = OwnershipInference.infer ~opts simple_res ast in
  let ownership_res = OwnershipSolver.solve_ownership ~opts infer_res in
  match ownership_res with
  | None -> Unverified Aliasing
  | Some o_res ->
    let o_hint = to_hint o_res infer_res.op_record in
    let solve = get_solve ~opts in
    let ans = solve ~opts simple_res o_hint ast in
    solver_result_to_check_result ans

let ownership ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_op = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_op ast in
  print_fold_locations simple_res;
  let infer_res = OwnershipInference.infer ~opts simple_res ast in
  print_inference infer_res ast;
  let ownership_res = OwnershipSolver.solve_ownership ~opts infer_res in
  print_ownership ownership_res infer_res ast;
  match ownership_res with
  | None -> Unverified Aliasing
  | Some _ -> Verified

let typecheck ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_op = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_op ast in
  print_typecheck simple_res ast;
  Verified

let interp ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_typing = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_typing ast in
  ignore simple_res;
  let open Interpreter in
  pp_val (eval_prog ast) Format.std_formatter;
  Format.pp_print_newline Format.std_formatter ();
  Verified

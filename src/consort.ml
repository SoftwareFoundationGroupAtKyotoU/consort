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

let typecheck ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_op = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_op ast in
  let f_types, side = simple_res in
  let open Ast in
  let open PrettyPrint in
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
    | _ -> pblock
             ~nl:true
             ~op:(ps "/*")
             ~body:(psep_gen newline ty_list)
             ~close:(ps "*/") in
  let annot (id, _) e =
    match Std.IntMap.find_opt id side.let_types, e with
    | Some ty, Let (patt, _, _) -> from_ty_patt ty patt
    | _ -> null in
  AstPrinter.pretty_print_program ~with_labels:true ~annot_fn ~annot stdout ast;
  Verified

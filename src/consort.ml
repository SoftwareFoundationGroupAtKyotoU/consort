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

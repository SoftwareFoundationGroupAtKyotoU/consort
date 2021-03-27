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

let reason_to_string = function
  | Aliasing -> "ownership"
  | Timeout -> "timeout"
  | Unsafe -> "unsafe"
  | Unknown -> "unknown"
  | SolverError s ->  "solver: \"" ^ s ^ "\""
  | UnhandledSolverOutput s -> "unexpected solver output: \"" ^ s ^ "\""

let result_to_string = function
  | Verified -> "VERIFIED"
  | Unverified r -> Printf.sprintf "UNVERIFIED (%s)" @@ reason_to_string r

let infer_ownership opts simple_res ast =
  let module OI = OwnershipInference in
  let o_result = OI.infer ~opts simple_res ast in
  match OwnershipSolver.solve_ownership ~opts (o_result.OI.Result.ovars,o_result.OI.Result.ocons,o_result.OI.Result.max_vars) with
  | None -> None
  | Some o_soln ->
    let map_ownership = function
      | OwnershipSolver.OVar v -> List.assoc v o_soln
      | OwnershipSolver.OConst c -> c
    in
    let o_hints = {
      OI.splits = OI.SplitMap.map (fun (a,b) ->
          (map_ownership a,map_ownership b)
        ) o_result.OI.Result.op_record.OI.splits;
      OI.gen = OI.GenMap.map map_ownership o_result.OI.Result.op_record.gen
    } in
    Some o_hints

let choose_solver opts =
  match opts.ArgOptions.solver with
  | Eldarica -> EldaricaBackend.solve
  | Hoice -> HoiceBackend.solve
  | Null -> NullSolver.solve
  | Parallel -> ParallelBackend.solve
  | Spacer -> HornBackend.solve
  | Z3SMT -> SmtBackend.solve

let check_file ?(opts=ArgOptions.default) in_name =
  let ast = AstUtil.parse_file in_name in
  let simple_typing = RefinementTypes.to_simple_funenv (ArgOptions.get_intr opts).op_interp in
  let ((program_types,_) as simple_res)= SimpleChecker.typecheck_prog simple_typing ast in
  if opts.debug_ast then begin
    AstPrinter.pretty_print_program stderr ast;
    StringMap.iter (fun n a ->
        Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
      ) program_types;
    flush stderr
  end;
  let infer_opt = infer_ownership opts simple_res ast in
  match infer_opt with
  | None -> Unverified Aliasing
  | Some r ->
    let module Backend = struct
      let solve = choose_solver opts
    end in
    let module S = FlowBackend.Make(Backend) in
    let ans = S.solve ~opts simple_res r ast in
    match ans with
    | Sat _ -> Verified
    | Unsat -> Unverified Unsafe
    | Timeout -> Unverified Timeout
    | Unhandled msg -> Unverified (UnhandledSolverOutput msg)
    | Error s -> Unverified (SolverError s)
    | Unknown -> Unverified Unknown

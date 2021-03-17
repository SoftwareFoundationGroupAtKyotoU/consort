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

module Options = struct
  type t = ArgOptions.t

  type arg_spec = (string * Arg.spec * string) list * (?comb:t -> unit -> t)

  let (>>) ((a1,f1) : arg_spec) ((a2,f2) : arg_spec) =
    let open ArgOptions in
    (a1 @ a2, (fun ?(comb=default) () ->
         f2 ~comb:(f1 ~comb ()) ()))

  let seq f o =
    (o >> f ())
end

let infer_ownership opts intr simple_res ast =
  let open ArgOptions in
  let module OI = OwnershipInference in
  let o_result = OI.infer ~opts:opts.relaxed_mode simple_res intr.Intrinsics.op_interp ast in
  match OwnershipSolver.solve_ownership ~opts:opts.own_solv_opts (o_result.OI.Result.ovars,o_result.OI.Result.ocons,o_result.OI.Result.max_vars) with
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
(*
let check_triviality res ast t =
  let rec is_trivial_refinemnt ss =
    let open RefinementTypes in
    function
    | Pred (nm,_)
    | CtxtPred(_,nm,_) ->
      StringSet.mem nm ss
    | And (r1,r2) -> (is_trivial_refinemnt ss r1) && (is_trivial_refinemnt ss r2)
    | _ -> false
  in
  let has_trivial_ref ss =
    let open RefinementTypes in
    fold_refinements (fun acc r ->
      acc || (is_trivial_refinemnt ss r)
    ) false
  in
  let env_is_trivial ss =
    StringMap.exists (fun _ t ->
      has_trivial_ref ss t
    )
  in
  let check_model m_raw =
    let open Sexplib.Sexp in
    let m = of_string m_raw in
    match m with
    | List (Atom "model"::l) ->
      let triv_preds = List.fold_left (fun acc sexp ->
          match sexp with
          | List (Atom "define-fun"::Atom nm::rem) -> begin
            let rem_len = List.length rem in
            let final = List.nth rem @@ rem_len - 1 in
            match final with
            | Atom "false" -> nm::acc
            | _ -> acc
            end
          | _ -> acc
        ) [] l
      in
      if List.length triv_preds = 0 then
        ()
      else begin
        let pred_set = StringSet.of_list triv_preds in
        Printf.fprintf stderr "!!!! Inferred trivial solution (check grounding?) !!!!\n";
        AstPrinter.pretty_print_program ~with_labels:true ~annot:(fun (id,_) _ ->
          let envs = res.Inference.Result.ty_envs in
          Hashtbl.find_opt envs id
          |> Option.map @@ env_is_trivial pred_set
          |> Fun.flip Option.bind @@ (fun flg ->
              let open PrettyPrint in
              if flg then
                Some (pl [ ps "// TRIVIAL"; newline ])
              else
                None
            )
          |> Option.value ~default:(PrettyPrint.null)
        ) stderr ast;
        let bad_preds = String.concat ", " triv_preds in
        failwith @@ Printf.sprintf "Solution contains trivial solutions for %s" bad_preds
      end
    | _ -> ()
  in
  if (not t) then Option.iter (fun _ -> ())
  else
    Option.iter check_model
*)
let print_model t =
  if t then
    Option.iter (fun s -> prerr_endline s; flush stderr)
  else
    Option.iter (fun _ -> ())

let check_file ?(opts=ArgOptions.default) ?(intrinsic_defn=Intrinsics.empty) in_name =
  let ast = AstUtil.parse_file in_name in
  let intr = intrinsic_defn in
  let simple_typing = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let ((program_types,_) as simple_res)= SimpleChecker.typecheck_prog simple_typing ast in
  if opts.debug_ast then begin
    AstPrinter.pretty_print_program stderr ast;
    StringMap.iter (fun n a ->
        Printf.fprintf stderr "%s: %s\n" n @@ SimpleTypes.fntype_to_string a
      ) program_types;
    flush stderr
  end;
  let infer_opt = infer_ownership opts intr simple_res ast in
  match infer_opt with
  | None -> Unverified Aliasing
  | Some r ->
    let solver =
      match opts.solver with
      | Spacer -> HornBackend.solve
      | Z3SMT -> SmtBackend.solve
      | Hoice -> HoiceBackend.solve
      | Null -> NullSolver.solve
      | Eldarica -> EldaricaBackend.solve
      | Parallel -> ParallelBackend.solve
    in
    let module Backend = struct
      let solve =
        solver
          ~opts:opts.solver_opts
          ~debug_cons:opts.debug_cons
          ?save_cons:opts.save_cons
          ~get_model:(opts.print_model || opts.check_trivial)
    end in
    let module S = FlowBackend.Make(Backend) in
    let (_,ans) = S.solve ~opts:S.({relaxed = opts.relaxed_mode; null_checks = opts.null_checks}) ~dump_ir:opts.dump_ir ~annot_infr:opts.annot_infr ~intr:intrinsic_defn simple_res r ast in
    let open Solver in
    match ans with
    | Sat m ->
      (*      check_triviality state ast opts.check_trivial m;*)
      print_model opts.print_model m;
      Verified
    | Unsat -> Unverified Unsafe
    | Timeout -> Unverified Timeout
    | Unhandled msg -> Unverified (UnhandledSolverOutput msg)
    | Error s -> Unverified (SolverError s)
    | Unknown -> Unverified Unknown

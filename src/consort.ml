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
  type solver =
    | Hoice
    | Spacer
    | Z3SMT
    | Eldarica
    | Parallel
    | Null

  type mode =
    | Unified
    | Refinement

  type t = {
    debug_cons: bool;
    debug_ast: bool;
    save_cons: string option;
    annot_infr: bool;
    print_model: bool;
    check_trivial: bool;
    dry_run : bool;
    solver: solver;
    mode: mode;
    solver_opts: Solver.options;
    own_solv_opts: OwnershipSolver.options;
    dump_ir : string option;
  }

  type arg_spec = (string * Arg.spec * string) list * (?comb:t -> unit -> t)

  let default = {
    debug_cons = false;
    save_cons = None;
    debug_ast = false;
    annot_infr = false;
    print_model = false;
    check_trivial = false;
    dry_run = false;
    solver = Spacer;
    mode = Refinement;
    solver_opts = Solver.default;
    own_solv_opts = OwnershipSolver.default;
    dump_ir = None;
  }

  let string_opt r =
    Arg.String (fun s -> r := Some s)

  let debug_arg_gen () =
    let open Arg in
    let debug_cons = ref default.debug_cons in
    let debug_ast = ref default.debug_ast in
    let show_model = ref default.print_model in
    let annot_infr = ref default.annot_infr in
    let dry_run = ref default.dry_run in
    let save_cons = ref default.save_cons in
    let all_debug_flags = [ debug_cons; debug_ast; show_model ] in
    let mk_arg key flg what =
      [
        ("-no-" ^ key, Clear flg, Printf.sprintf "Do not print %s" what);
        ("-show-" ^key, Set flg, Printf.sprintf "Print %s on stderr" what)
      ] in
    let arg_defs =
      (mk_arg "cons" debug_cons "constraints sent to Z3") @
        (mk_arg "ast" debug_ast "(low-level) AST") @
        (mk_arg "model" show_model "inferred model") @
        [
          ("-annot-infer", Set annot_infr, "Print an annotated AST program with the inferred types on stderr");
          ("-dry-run", Set dry_run, "Parse, typecheck, and run inference, but do not actually run Z3");
          ("-show-model", Set show_model, "Print model produced from successful verification");
          ("-sigh", Unit (fun () -> save_cons := Some "sigh.smt"), "Here we go again...");
          ("-save-cons", string_opt save_cons, "Save constraints in <file>");
          ("-show-all", Unit (fun () ->
             List.iter (fun r -> r := true) all_debug_flags;
             Log.all ();
           ), "Show all debug output");
          ("-none", Unit (fun () ->
             List.iter (fun r -> r:= false) all_debug_flags;
             Log.disable ()
           ), "Suppress all debug output");
          ("-debug", String (fun s ->
             Log.filter @@ List.map String.trim @@ String.split_on_char ',' s
           ), "Debug sources s1,s2,...");
          ("-debug-all", Unit Log.all, "Show all debug output")
        ] in
    (arg_defs, (fun ?(comb=default) () ->
       { comb with
         debug_ast = !debug_ast;
         print_model = !show_model;
         annot_infr = !annot_infr;
         debug_cons = !debug_cons;
         save_cons = !save_cons;
         dry_run = !dry_run
       }))

  let (>>) ((a1,f1) : arg_spec) ((a2,f2) : arg_spec) =
    (a1 @ a2, (fun ?(comb=default) () ->
       f2 ~comb:(f1 ~comb ()) ()))

  let seq f o =
    (o >> f ())

  let solver_arg_gen () =
    let open Arg in
    let check_trivial = ref default.check_trivial in
    let solver = ref default.solver in
    let mode = ref default.mode in
    let dump_ir = ref default.dump_ir in
    ([
      ("-seq-solver", Unit (fun () -> prerr_endline "WARNING: seq solver option is deprecated and does nothing"), "(DEPRECATED) No effect");
      ("-check-triviality", Set check_trivial, "Check if produced model is trivial");
      ("-mode", Symbol (["refinement"; "unified"], function
         | "refinement" -> mode := Refinement
         | "unified" -> mode := Unified
         | _ -> assert false
       ), " Use mode <mode>. (default: refinement)");
      ("-dump-ir", string_opt dump_ir, "Dump intermediate relations and debugging information (only implemented in unified)");
      ("-solver", Symbol (["spacer";"hoice";"z3";"null";"eldarica";"parallel"], function
         | "spacer" -> solver := Spacer
         | "hoice" -> solver := Hoice
         | "null" -> solver := Null
         | "z3" -> solver := Z3SMT
         | "eldarica" -> solver := Eldarica
         | "parallel" -> solver := Parallel
         | _ -> assert false), " Use solver backend <solver>. (default: spacer)")
    ], (fun ?(comb=default) () ->
       let () =
           match !dump_ir,!mode with
           | Some _, Refinement -> prerr_endline "Warning! dump-ir has no effect in refinement mode (use unified)"
           | _ -> ()
       in
       { comb with
         check_trivial = !check_trivial;
         solver = !solver;
         mode = !mode;
         dump_ir = !dump_ir
       }))

  let solver_opt_gen () =
    let (l,g) = Solver.opt_gen () in
    let (l2,g2) = OwnershipSolver.ownership_arg_gen () in
    (l @ l2, (fun ?(comb=default) () ->
       { comb with
         solver_opts = g ~comb:comb.solver_opts ();
         own_solv_opts = g2 ~comb:comb.own_solv_opts ()
       }))
end

let infer_ownership opts intr simple_res ast =
  let open Options in
  let module OI = OwnershipInference in
  let o_result = OI.infer simple_res intr.Intrinsics.op_interp ast in
  match OwnershipSolver.solve_ownership ~opts:opts.own_solv_opts (o_result.OI.Result.ovars,o_result.OI.Result.ocons) with
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


module type SOLVER = sig
  type t
  val solve : annot_infr:bool -> dump_ir:(string option) -> intr:Intrinsics.interp_t -> SimpleChecker.simple_results -> float OwnershipInference.ownership_ops -> Ast.prog -> (t * Solver.result)
    
end

let check_file ?(opts=Options.default) ?(intrinsic_defn=Intrinsics.empty) in_name =
  let open Options in
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
    let s_mod =
      match opts.mode with
      | Unified -> (module FlowBackend.Make(Backend) : SOLVER)
      | Refinement ->
        (module TypeInference.Make(Backend) : SOLVER)
    in
    let module S = (val s_mod : SOLVER) in
    let (_,ans) = S.solve ~dump_ir:opts.dump_ir ~annot_infr:opts.annot_infr ~intr:intrinsic_defn simple_res r ast in
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

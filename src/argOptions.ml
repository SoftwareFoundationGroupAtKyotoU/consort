module Solver = struct
  type choice =
    | Hoice
    | Spacer
    | Z3SMT
    | Eldarica
    | Parallel
    | Null
  type options = {
    timeout : int;
    command : string option;
    command_extra : string option;
  }

  let default = {
    timeout = 30;
    command = None;
    command_extra = None
  }
end

type t = {
  debug_cons : bool;
  debug_ast : bool;
  save_cons : string option;
  annot_infr : bool;
  print_model : bool;
  dry_run : bool;
  check_trivial : bool;
  solver : Solver.choice;
  dump_ir : string option;
  relaxed_mode : bool;
  omit_havoc : bool;
  null_checks : bool;
  solver_opts : Solver.options;
  intrinsics : Intrinsics.interp_t;
  expect_typing : bool;
  cfa : int;
  verbose : bool;
  file_list : Arg.usage_msg list;
  exit_status : bool;
}
type arg_spec = Arg.key * Arg.spec * Arg.doc
type arg_update = ?opts:t -> unit -> t
type arg_gen = arg_spec list * arg_update

let default = {
  debug_cons = false;
  debug_ast = false;
  save_cons = None;
  annot_infr = false;
  print_model = false;
  dry_run = false;
  check_trivial = false;
  solver = Spacer;
  dump_ir = None;
  relaxed_mode = false;
  omit_havoc = false;
  null_checks = false;
  solver_opts = Solver.default;
  intrinsics = Intrinsics.empty;
  expect_typing = true;
  cfa = 1;
  verbose = false;
  file_list = [];
  exit_status = false;
}
let get_model opts = opts.print_model || opts.check_trivial
let spec_seq (g2 : unit -> arg_gen) (g1 : arg_gen) =
  let s1, f1 = g1 in
  let s2, f2 = g2 () in
  let spec = s1 @ s2 in
  let update ?(opts=default) () = f2 ~opts:(f1 ~opts ()) () in
  (spec, update)
let debug_arg_gen () =
  let open Arg in
  let debug_cons = ref default.debug_cons in
  let debug_ast = ref default.debug_ast in
  let save_cons = ref default.save_cons in
  let annot_infr = ref default.annot_infr in
  let print_model = ref default.print_model in
  let dry_run = ref default.dry_run in
  let all_debug_flags = [ debug_cons; debug_ast; annot_infr; print_model ] in
  let mk_arg key flg what = [
    ("-no-" ^ key, Clear flg, Printf.sprintf "Do not print %s" what);
    ("-show-" ^ key, Set flg, Printf.sprintf "Print %s on stderr" what)
  ] in
  let spec =
    (mk_arg "cons" debug_cons "constraints sent to Z3") @
    (mk_arg "ast" debug_ast "(low-level) AST") @
    (mk_arg "model" print_model "inferred model produced from successful verification") @ [
      ("-annot-infer", Set annot_infr,
       "Print an annotated AST program with the inferred types on stderr");
      ("-dry-run", Set dry_run,
       "Parse, typecheck, and run inference, but do not actually run Z3");
      ("-sigh", Unit (fun () -> save_cons := Some "sigh.smt"),
       "Here we go again...");
      ("-save-cons", String (fun s -> save_cons := Some s),
       "Save constraints in <file>");
      ("-show-all", Unit (fun () ->
           List.iter (fun r -> r := true) all_debug_flags;
           Log.all ()),
       "Show all debug output");
      ("-none", Unit (fun () ->
           List.iter (fun r -> r:= false) all_debug_flags;
           Log.disable ()),
       "Suppress all debug output");
      ("-debug", String (fun s ->
           Log.filter @@ List.map String.trim @@ String.split_on_char ',' s),
       "Debug sources s1,s2,...");
      ("-debug-all", Unit Log.all, "Show all debug output")
    ] in
  let update ?(opts=default) () = {
    opts with
    debug_cons = !debug_cons;
    debug_ast = !debug_ast;
    save_cons = !save_cons;
    annot_infr = !annot_infr;
    print_model = !print_model;
    dry_run = !dry_run
  } in
  (spec, update)
let infr_arg_gen () =
  let relaxed_mode = ref default.relaxed_mode in
  let open Arg in
  let spec = [
    ("-relaxed-max", Unit (fun () -> relaxed_mode := true),
     "Use alternative, relaxed maximization constraints")
  ] in
  let update ?(opts=default) () = {
    opts with relaxed_mode = !relaxed_mode
  } in
  (spec, update)
let opt_gen ?nm ?(solv_nm="solver") () =
  let open Arg in
  let pref = Option.map (fun s -> s ^ "-") nm |> Option.value ~default:"" in
  let timeout = ref default.solver_opts.timeout in
  let command = ref default.solver_opts.command in
  let extra = ref default.solver_opts.command_extra in
  let spec = [
    ("-" ^ pref ^ "timeout", Set_int timeout,
     Printf.sprintf "Timeout for %s in seconds" solv_nm);
    ("-" ^ pref ^ "command", String (fun s -> command := Some s),
     Printf.sprintf "Executable for %s" solv_nm);
    ("-" ^ pref ^ "solver-args", String (fun s -> extra := Some s),
     Printf.sprintf "Extra arguments to pass wholesale to %s" solv_nm)
  ] in
  let update ?(opts=default) () = {
    opts with solver_opts = {
      timeout = !timeout;
      command = !command;
      command_extra = !extra
    }
  } in
  (spec, update)
let ownership_arg_gen () = opt_gen ~nm:"o" ~solv_nm:"ownership solver" ()
let solver_arg_gen () =
  let check_trivial = ref default.check_trivial in
  let solver = ref default.solver in
  let dump_ir = ref default.dump_ir in
  let omit_havoc = ref default.omit_havoc in
  let null_checks = ref default.null_checks in
  let open Arg in
  let spec = [
    ("-seq-solver", Unit (fun () ->
         prerr_endline "WARNING: seq solver option is deprecated and does nothing"),
     "(DEPRECATED) No effect");
    ("-check-triviality", Set check_trivial,
     "Check if produced model is trivial");
    ("-mode", Symbol (["refinement"; "unified"], fun _ ->
         prerr_endline "WARNING: the mode option is deprecated and does nothing"),
     " (DEPRECATED) No effect");
    ("-dump-ir", String (fun s -> dump_ir := Some s),
     "Dump intermediate relations and debugging information (only implemented in unified)");
    ("-omit-havoc", Set omit_havoc,
     "Omit havoced access paths from the generated CHC (implies relaxed-max) (EXPERIMENTAL)");
    ("-check-null", Set null_checks,
     "For freedom of null pointer exceptions");
    ("-solver",
     Symbol (["spacer";"hoice";"z3";"null";"eldarica";"parallel"], function
         | "spacer" -> solver := Spacer
         | "hoice" -> solver := Hoice
         | "null" -> solver := Null
         | "z3" -> solver := Z3SMT
         | "eldarica" -> solver := Eldarica
         | "parallel" -> solver := Parallel
         | _ -> assert false),
     " Use solver backend <solver>. (default: spacer)")
  ] in
  let update ?(opts=default) () = {
    opts with
    check_trivial = !check_trivial;
    solver = !solver;
    dump_ir = !dump_ir;
    relaxed_mode = !omit_havoc;
    omit_havoc = !omit_havoc;
    null_checks = !null_checks
  } in
  spec_seq infr_arg_gen (spec, update)
let solver_opt_gen () =
  ownership_arg_gen () |> spec_seq opt_gen
let intrinsics_arg_gen () =
  let open Arg in
  let f_name = ref None in
  let spec = [
    "-intrinsics", String (fun x -> f_name := Some x),
    "Load definitions of standard operations from <file>"
  ] in
  let update ?(opts=default) () = {
    opts with intrinsics = Intrinsics.option_loader !f_name
  } in
  (spec, update)
let test_suite_arg_gen () =
  let open Arg in
  let expect = ref default.expect_typing in
  let verbose = ref default.verbose in
  let cfa = ref default.cfa in
  let file_list = ref default.file_list in
  let spec = [
    ("-neg", Clear expect, "Expect typing failures");
    ("-pos", Set expect, "Expect typing success (default)");
    ("-cfa", Set_int cfa, "k to use for k-cfa inference");
    ("-verbose", Set verbose, "Provide more output");
    ("-files", Rest (fun s -> file_list := s::!file_list),
     "Interpret all remaining arguments as files to test")
  ] in
  let update ?(opts=default) () = {
    opts with
    expect_typing = !expect;
    cfa = !cfa;
    verbose = !verbose;
    file_list = !file_list
  } in
  (spec, update)
let test_arg_gen () =
  let open Arg in
  let cfa = ref default.cfa in
  let status = ref default.exit_status in
  let spec = [
    ("-cfa", Set_int cfa, "k to use for k-cfa inference");
    ("-exit-status", Set status,
     "Indicate successful verification with exit code");
  ] in
  let update ?(opts=default) () = {
    opts with
    cfa = !cfa;
  } in
  (spec, update)

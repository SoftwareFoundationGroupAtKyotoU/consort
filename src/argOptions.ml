module Cache = struct
  type 'a t = 'a option ref

  let init = ref None
  let get c f =
    match !c with
    | None -> let v = f() in c := Some v; v
    | Some v -> v
end

module Solver = struct
  type t =
    | Eldarica
    | Hoice
    | Null
    | Parallel
    | Spacer
    | Z3SMT

  let pairs = [
    ("eldarica", Eldarica);
    ("hoice", Hoice);
    ("null", Null);
    ("parallel", Parallel);
    ("spacer", Spacer);
    ("z3smt", Z3SMT)
  ]
  let candidates = List.map (fun (s, _) -> s) pairs
  let update solver cand = solver := List.assoc cand pairs
end

type t = {
  debug_cons : bool;
  debug_ast : bool;
  save_cons : string option;
  annot_infr : bool;
  print_model : bool;
  dry_run : bool;
  solver : Solver.t;
  timeout : int;
  command : string option;
  command_extra : string option;
  dump_ir : string option;
  relaxed_mode : bool;
  null_checks : bool;
  intrinsics_file : string option;
  intrinsics : Intrinsics.interp_t Cache.t;
  expect_typing : bool;
  cfa : int;
  verbose : bool;
  file_list : Arg.usage_msg list;
  exit_status : bool;
  yaml : bool;
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
  solver = Spacer;
  timeout = 30;
  command = None;
  command_extra = None;
  dump_ir = None;
  relaxed_mode = false;
  null_checks = false;
  intrinsics_file = None;
  intrinsics = Cache.init;
  expect_typing = true;
  cfa = 1;
  verbose = false;
  file_list = [];
  exit_status = false;
  yaml = false;
}
let get_intr opts =
  let option_loader () =
    match opts.intrinsics_file with
    | None -> Intrinsics.empty
    | Some f -> Intrinsics.load f in
  Cache.get opts.intrinsics option_loader
let arg_gen () =
  let debug_cons = ref default.debug_cons in
  let debug_ast = ref default.debug_ast in
  let save_cons = ref default.save_cons in
  let annot_infr = ref default.annot_infr in
  let print_model = ref default.print_model in
  let dry_run = ref default.dry_run in
  let solver = ref default.solver in
  let timeout = ref default.timeout in
  let command = ref default.command in
  let extra = ref default.command_extra in
  let dump_ir = ref default.dump_ir in
  let relaxed_mode = ref default.relaxed_mode in
  let null_checks = ref default.null_checks in
  let f_name = ref None in
  let expect = ref default.expect_typing in
  let cfa = ref default.cfa in
  let verbose = ref default.verbose in
  let file_list = ref default.file_list in
  let status = ref default.exit_status in
  let yaml = ref default.yaml in
  let all_debug_flags = [ debug_cons; debug_ast; annot_infr; print_model ] in
  let open Arg in
  let spec = [
    ("-show-cons", Set debug_cons, "Print constraints sent to Z3 on stderr");
    ("-show-ast", Set debug_ast, "Print (low-level) AST on stderr");
    ("-show-model", Set print_model, "Print inferred model produced from successful verification on stderr");
    ("-annot-infer", Set annot_infr,
     "Print an annotated AST program with the inferred types on stderr");
    ("-dry-run", Set dry_run,
     "Parse, typecheck, and run inference, but do not actually run Z3");
    ("-save-cons", String (fun s -> save_cons := Some s),
     "Save constraints in <file>");
    ("-show-all", Unit (fun () ->
         List.iter (fun r -> r := true) all_debug_flags;
         Log.all ()),
     "Show all debug output");
    ("-debug", String (fun s ->
         Log.filter @@ List.map String.trim @@ String.split_on_char ',' s),
     "Debug sources s1,s2,...");
    ("-debug-all", Unit Log.all, "Show all debug output");
    ("-solver",
     Symbol (Solver.candidates, Solver.update solver),
     " Use solver backend <solver>. (default: spacer)");
    ("-dump-ir", String (fun s -> dump_ir := Some s),
     "Dump intermediate relations and debugging information");
    ("-relaxed-max", Unit (fun () -> relaxed_mode := true),
     "Use alternative, relaxed maximization constraints");
    ("-check-null", Set null_checks,
     "For freedom of null pointer exceptions");
    ("-timeout", Set_int timeout, "Timeout for solver in seconds");
    ("-command", String (fun s -> command := Some s), "Executable for solver");
    ("-solver-args", String (fun s -> extra := Some s),
     "Extra arguments to pass wholesale to solver");
    ("-intrinsics", String (fun x -> f_name := Some x),
     "Load definitions of standard operations from <file>");
    ("-neg", Clear expect, "Expect typing failures");
    ("-pos", Set expect, "Expect typing success (default)");
    ("-cfa", Set_int cfa, "k to use for k-cfa inference");
    ("-verbose", Set verbose, "Provide more output");
    ("-files", Rest (fun s -> file_list := s::!file_list),
     "Interpret all remaining arguments as files to test");
    ("-exit-status", Set status,
     "Indicate successful verification with exit code");
    ("-yaml", Set yaml, "Print verification result in YAML format");
  ] in
  let update () = {
    default with
    debug_cons = !debug_cons;
    debug_ast = !debug_ast;
    save_cons = !save_cons;
    annot_infr = !annot_infr;
    print_model = !print_model;
    dry_run = !dry_run;
    solver = !solver;
    timeout = !timeout;
    command = !command;
    command_extra = !extra;
    dump_ir = !dump_ir;
    relaxed_mode = !relaxed_mode;
    null_checks = !null_checks;
    intrinsics_file = !f_name;
    expect_typing = !expect;
    cfa = !cfa;
    verbose = !verbose;
    file_list = !file_list;
    exit_status = !status;
    yaml = !yaml;
  } in
  (spec, update)

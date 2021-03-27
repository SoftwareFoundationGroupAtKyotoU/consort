module Cache = struct
  type 'a t = 'a option ref

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
  output_file : string option;
  show_annot : bool;
  show_ast : bool;
  show_ir : bool;
  debug_cons : bool;
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
  expect_typing : bool;
  cfa : int;
  verbose : bool;
  file_list : Arg.usage_msg list;
  exit_status : bool;
  yaml : bool;
  output_channel : out_channel Cache.t;
  intrinsics : Intrinsics.interp_t Cache.t;
}

let default = {
  output_file = None;
  show_annot = false;
  show_ast = false;
  show_ir = false;
  debug_cons = false;
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
  expect_typing = true;
  cfa = 1;
  verbose = false;
  file_list = [];
  exit_status = false;
  yaml = false;
  output_channel = ref None;
  intrinsics = ref None;
}
let show flag opts print =
  if flag then
    let out = Cache.get opts.output_channel (fun () ->
        Option.fold ~none:stderr ~some:open_out opts.output_file) in
    print out; flush out
  else ()
let show_annot opts = show opts.show_annot opts
let show_ast opts = show opts.show_ast opts
let show_cons opts = show opts.debug_cons opts
let show_ir opts = show opts.show_ir opts
let show_model opts = show opts.print_model opts
let get_intr opts =
  let option_loader () =
    match opts.intrinsics_file with
    | None -> Intrinsics.empty
    | Some f -> Intrinsics.load f in
  Cache.get opts.intrinsics option_loader
let arg_gen () =
  let output_file = ref default.output_file in
  let show_annot = ref default.show_annot in
  let show_ast = ref default.show_ast in
  let show_ir = ref default.show_ir in
  let debug_cons = ref default.debug_cons in
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
  let all_debug_flags = [ show_annot; show_ast; debug_cons; print_model ] in
  let open Arg in
  let spec = [
    ("-output-file", String (fun s -> output_file := Some s),
     "Alternative output target other than stderr for -show-<something> options");
    ("-show-annot", Set show_annot,
     "Print an annotated AST program with the inferred types on stderr");
    ("-show-ast", Set show_ast, "Print (low-level) AST on stderr");
    ("-show-ir", Set show_ir,
     "Print intermediate relations and debugging information");
    ("-show-cons", Set debug_cons, "Print constraints sent to Z3 on stderr");
    ("-show-model", Set print_model, "Print inferred model produced from successful verification on stderr");
    ("-dry-run", Set dry_run,
     "Parse, typecheck, and run inference, but do not actually run Z3");
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
    output_file = !output_file;
    show_annot = !show_annot;
    show_ast = !show_ast;
    show_ir = !show_ir;
    debug_cons = !debug_cons;
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
    output_channel = default.output_channel;
    intrinsics = default.intrinsics;
  } in
  (spec, update)

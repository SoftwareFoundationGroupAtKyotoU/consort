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
  show_cons : bool;
  show_ir : bool;
  show_model : bool;
  dry_run : bool;
  relaxed_mode : bool;
  null_checks : bool;
  expect_typing : bool;
  exit_status : bool;
  yaml : bool;
  verbose : bool;
  solver : Solver.t;
  timeout : int;
  command : string option;
  command_extra : string option;
  cfa : int;
  intrinsics_file : string option;
  file_list : Arg.usage_msg list;
  output_channel : out_channel Cache.t;
  intrinsics : Intrinsics.interp_t Cache.t;
}

let default = {
  output_file = None;
  show_annot = false;
  show_ast = false;
  show_cons = false;
  show_ir = false;
  show_model = false;
  dry_run = false;
  relaxed_mode = false;
  null_checks = false;
  expect_typing = true;
  exit_status = false;
  yaml = false;
  verbose = false;
  solver = Spacer;
  timeout = 30;
  command = None;
  command_extra = None;
  cfa = 1;
  intrinsics_file = None;
  file_list = [];
  output_channel = ref None;
  intrinsics = ref None;
}
let show ~opts flag print =
  if flag then
    let out = Cache.get opts.output_channel (fun () ->
        Option.fold ~none:stderr ~some:open_out opts.output_file) in
    print out; flush out
  else ()
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
  let show_cons = ref default.show_cons in
  let show_ir = ref default.show_ir in
  let show_model = ref default.show_model in
  let dry_run = ref default.dry_run in
  let relaxed_mode = ref default.relaxed_mode in
  let null_checks = ref default.null_checks in
  let expect = ref default.expect_typing in
  let status = ref default.exit_status in
  let yaml = ref default.yaml in
  let verbose = ref default.verbose in
  let solver = ref default.solver in
  let timeout = ref default.timeout in
  let command = ref default.command in
  let extra = ref default.command_extra in
  let cfa = ref default.cfa in
  let f_name = ref None in
  let file_list = ref default.file_list in
  let show_all () =
    let all = [show_annot; show_ast; show_cons; show_ir; show_model] in
    List.iter (fun r -> r := true) all; Log.all () in
  let debug s =
    Log.filter @@ List.map String.trim @@ String.split_on_char ',' s in
  let set_string r =
    Arg.String (fun s -> r := Some s) in
  let open Arg in
  let spec = [
    ("-output-file", String (fun s -> output_file := Some s),
     "Alternative output target other than stderr for -show-<something> options");
    ("-show-annot", Set show_annot,
     "Print an annotated AST program with the inferred types on stderr");
    ("-show-ast", Set show_ast,
     "Print (low-level) AST on stderr");
    ("-show-cons", Set show_cons,
     "Print constraints sent to solver on stderr");
    ("-show-ir", Set show_ir,
     "Print intermediate relations and debugging information");
    ("-show-model", Set show_model,
     "Print inferred model produced from successful verification on stderr");
    ("-show-all", Unit show_all,
     "Print all debug output");
    ("-debug", String debug,
     "Debug sources s1,s2,...");
    ("-debug-all", Unit Log.all,
     "Show all debug output");
    ("-dry-run", Set dry_run,
     "Parse, typecheck, and run inference, but do not actually run Z3");
    ("-relaxed-max", Set relaxed_mode,
     "Use alternative, relaxed maximization constraints");
    ("-check-null", Set null_checks,
     "For freedom of null pointer exceptions");
    ("-pos", Set expect,
     "Expect typing success (default)");
    ("-neg", Clear expect,
     "Expect typing failures");
    ("-exit-status", Set status,
     "Indicate successful verification with exit code");
    ("-yaml", Set yaml,
     "Print verification result in YAML format");
    ("-verbose", Set verbose,
     "Provide more output");
    ("-solver", Symbol (Solver.candidates, Solver.update solver),
     " Use solver backend <solver>. (default: spacer)");
    ("-timeout", Set_int timeout,
     "Timeout for solver in seconds");
    ("-command", set_string command,
     "Executable for solver");
    ("-solver-args", set_string extra,
     "Extra arguments to pass wholesale to solver");
    ("-cfa", Set_int cfa,
     "k to use for k-cfa inference");
    ("-intrinsics", set_string f_name,
     "Load definitions of standard operations from <file>");
    ("-files", Rest (fun s -> file_list := s::!file_list),
     "Interpret all remaining arguments as files to test");
  ] in
  let update () = {
    output_file = !output_file;
    show_annot = !show_annot;
    show_ast = !show_ast;
    show_cons = !show_cons;
    show_ir = !show_ir;
    show_model = !show_model;
    dry_run = !dry_run;
    relaxed_mode = !relaxed_mode;
    null_checks = !null_checks;
    expect_typing = !expect;
    exit_status = !status;
    yaml = !yaml;
    verbose = !verbose;
    solver = !solver;
    timeout = !timeout;
    command = !command;
    command_extra = !extra;
    cfa = !cfa;
    intrinsics_file = !f_name;
    file_list = !file_list;
    output_channel = default.output_channel;
    intrinsics = default.intrinsics;
  } in
  (spec, update)

module Cache = struct
  type 'a t = 'a option ref

  let get c f =
    match !c with
    | None -> let v = f() in c := Some v; v
    | Some v -> v
end

module ExecMode = struct
  type t =
    | Consort
    | Ownership
    | Typecheck
    | ConvMoCHi

  let pairs = [
    ("consort", Consort);
    ("ownership", Ownership);
    ("typecheck", Typecheck);
    ("convmochi", ConvMoCHi)
  ]
  let default = "consort"
  let candidates = List.map (fun (s, _) -> s) pairs
  let from_string s = List.assoc s pairs
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
  let default = "spacer"
  let candidates = List.map (fun (s, _) -> s) pairs
  let from_string s = List.assoc s pairs
end

type t = {
  exec_mode : ExecMode.t;
  output_file : string option;
  show_annot : bool;
  show_ast : bool;
  show_cons : bool;
  show_ir : bool;
  show_model : bool;
  dry_run : bool;
  relaxed_max : bool;
  check_null : bool;
  expect_typing : bool;
  exit_status : bool;
  yaml : bool;
  verbose : bool;
  solver : Solver.t;
  timeout : int;
  command : string option;
  solver_args : string option;
  cfa : int;
  intrinsics_file : string option;
  file_list : Arg.usage_msg list;
  output_channel : out_channel Cache.t;
  intrinsics : Intrinsics.interp_t Cache.t;
  ownership_arity : int;
}

let default = {
  exec_mode = ExecMode.from_string ExecMode.default;
  output_file = None;
  show_annot = false;
  show_ast = false;
  show_cons = false;
  show_ir = false;
  show_model = false;
  dry_run = false;
  relaxed_max = false;
  check_null = false;
  expect_typing = true;
  exit_status = false;
  yaml = false;
  verbose = false;
  solver = Solver.from_string Solver.default;
  timeout = 30;
  command = None;
  solver_args = None;
  cfa = 1;
  intrinsics_file = None;
  file_list = [];
  output_channel = ref None;
  intrinsics = ref None;
  ownership_arity = 1;
}
let close_output ~opts =
  Option.iter close_out !(opts.output_channel);
  opts.output_channel := None
let show ~opts flag print =
  if flag then
    let set f = Cache.get opts.output_channel (fun () -> open_out f) in
    let out = Option.fold ~none:stderr ~some:set opts.output_file in
    print out; flush out
  else ()
let get_intr opts =
  let open Intrinsics in
  let set f = Cache.get opts.intrinsics (fun () -> load f) in
  Option.fold ~none:empty ~some:set opts.intrinsics_file
let parse anon_fun usage_msg =
  let exec_mode = ref default.exec_mode in
  let output_file = ref default.output_file in
  let show_annot = ref default.show_annot in
  let show_ast = ref default.show_ast in
  let show_cons = ref default.show_cons in
  let show_ir = ref default.show_ir in
  let show_model = ref default.show_model in
  let show_all_flags = [show_annot; show_ast; show_cons; show_ir; show_model] in
  let dry_run = ref default.dry_run in
  let relaxed_max = ref default.relaxed_max in
  let check_null = ref default.check_null in
  let expect_typing = ref default.expect_typing in
  let exit_status = ref default.exit_status in
  let yaml = ref default.yaml in
  let verbose = ref default.verbose in
  let solver = ref default.solver in
  let timeout = ref default.timeout in
  let command = ref default.command in
  let solver_args = ref default.solver_args in
  let cfa = ref default.cfa in
  let intrinsics_file = ref None in
  let file_list = ref default.file_list in
  let ownership_arity = ref default.ownership_arity in
  let show_all () =
    List.iter (fun r -> r := true) show_all_flags; Log.all () in
  let debug s =
    Log.filter @@ List.map String.trim @@ String.split_on_char ',' s in
  let set_string r = Arg.String (fun s -> r := Some s) in
  let set_exec s = exec_mode := ExecMode.from_string s in
  let set_solver s = solver := Solver.from_string s in
  let open Arg in
  let spec = [
    ("-exec", Symbol (ExecMode.candidates, set_exec),
     Printf.sprintf "\t Choose execution mode (default: %s)" ExecMode.default);
    ("-output-file", String (fun s -> output_file := Some s),
     "<file>\t Output target of -show-* options instead of stderr");
    ("-show-annot", Set show_annot,
     "\t Print an annotated AST program with the inferred types");
    ("-show-ast", Set show_ast,
     "\t Print (low-level) AST");
    ("-show-cons", Set show_cons,
     "\t Print constraints sent to solver");
    ("-show-ir", Set show_ir,
     "\t Print intermediate relations and debugging information");
    ("-show-model", Set show_model,
     "\t Print inferred model produced from successful verification");
    ("-show-all", Unit show_all,
     "\t Print all debug output");
    ("-debug", String debug,
     "<s1>,<s2>,...\t Debug sources");
    ("-debug-all", Unit Log.all,
     "\t Show all debug output");
    ("-dry-run", Set dry_run,
     "\t Parse, typecheck, and run inference, but do not actually run solver (not implemented)");
    ("-relaxed-max", Set relaxed_max,
     "\t Use alternative, relaxed maximization constraints");
    ("-check-null", Set check_null,
     "\t For freedom of null pointer exceptions");
    ("-pos", Set expect_typing,
     "\t\t Expect typing success (default)");
    ("-neg", Clear expect_typing,
     "\t\t Expect typing failures");
    ("-exit-status", Set exit_status,
     "\t Indicate successful verification with exit code");
    ("-yaml", Set yaml,
     "\t Print verification result in YAML format");
    ("-verbose", Set verbose,
     "\t Provide more output");
    ("-solver", Symbol (Solver.candidates, set_solver),
     Printf.sprintf "\t Choose solver backend (default: %s)" Solver.default);
    ("-timeout", Set_int timeout,
     "<integer>\t Timeout for solver in seconds");
    ("-command", set_string command,
     "<string>\t Executable for solver");
    ("-solver-args", set_string solver_args,
     "<string>  Extra arguments to pass wholesale to solver");
    ("-cfa", Set_int cfa,
     "<integer>\t k to use for k-cfa inference");
    ("-intrinsics", set_string intrinsics_file,
     "<file>\t Load definitions of standard operations from <file>");
    ("-files", Rest (fun s -> file_list := s::!file_list),
     "<file> ...\t Interpret all remaining arguments as files to test");
    ("-ownership-arity", Set_int ownership_arity,
     "<integer>\t The number of different ownership variables used in recursive data structure (default: 1)");
  ] in
  Arg.parse spec anon_fun usage_msg;
  {
    exec_mode = !exec_mode;
    output_file = !output_file;
    show_annot = !show_annot;
    show_ast = !show_ast;
    show_cons = !show_cons;
    show_ir = !show_ir;
    show_model = !show_model;
    dry_run = !dry_run;
    relaxed_max = !relaxed_max;
    check_null = !check_null;
    expect_typing = !expect_typing;
    exit_status = !exit_status;
    yaml = !yaml;
    verbose = !verbose;
    solver = !solver;
    timeout = !timeout;
    command = !command;
    solver_args = !solver_args;
    cfa = !cfa;
    intrinsics_file = !intrinsics_file;
    file_list = !file_list;
    output_channel = default.output_channel;
    intrinsics = default.intrinsics;
    ownership_arity = !ownership_arity;
  }

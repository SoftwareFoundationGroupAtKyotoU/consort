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
  let default = "spacer"
  let candidates = List.map (fun (s, _) -> s) pairs
  let from_string s = List.assoc s pairs
end

type t = {
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
}

let default = {
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
let arg_gen () =
  let output_file = ref default.output_file in
  let show_annot = ref default.show_annot in
  let show_ast = ref default.show_ast in
  let show_cons = ref default.show_cons in
  let show_ir = ref default.show_ir in
  let show_model = ref default.show_model in
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
  let show_all () =
    let all = [show_annot; show_ast; show_cons; show_ir; show_model] in
    List.iter (fun r -> r := true) all; Log.all () in
  let debug s =
    Log.filter @@ List.map String.trim @@ String.split_on_char ',' s in
  let set_string r = Arg.String (fun s -> r := Some s) in
  let set_solver s = solver := Solver.from_string s in
  let open Arg in
  let spec = [
    ("-output-file", String (fun s -> output_file := Some s),
     " Alternative output target other than stderr for -show-<something> options");
    ("-show-annot", Set show_annot,
     " Print an annotated AST program with the inferred types on stderr");
    ("-show-ast", Set show_ast,
     " Print (low-level) AST on stderr");
    ("-show-cons", Set show_cons,
     " Print constraints sent to solver on stderr");
    ("-show-ir", Set show_ir,
     " Print intermediate relations and debugging information");
    ("-show-model", Set show_model,
     " Print inferred model produced from successful verification on stderr");
    ("-show-all", Unit show_all,
     " Print all debug output");
    ("-debug", String debug,
     " Debug sources s1,s2,...");
    ("-debug-all", Unit Log.all,
     " Show all debug output");
    ("-dry-run", Set dry_run,
     " Parse, typecheck, and run inference, but do not actually run Z3");
    ("-relaxed-max", Set relaxed_max,
     " Use alternative, relaxed maximization constraints");
    ("-check-null", Set check_null,
     " For freedom of null pointer exceptions");
    ("-pos", Set expect_typing,
     " Expect typing success (default)");
    ("-neg", Clear expect_typing,
     " Expect typing failures");
    ("-exit-status", Set exit_status,
     " Indicate successful verification with exit code");
    ("-yaml", Set yaml,
     " Print verification result in YAML format");
    ("-verbose", Set verbose,
     " Provide more output");
    ("-solver", Symbol (Solver.candidates, set_solver),
     Printf.sprintf " Use solver backend <solver>. (default: %s)" Solver.default);
    ("-timeout", Set_int timeout,
     " Timeout for solver in seconds");
    ("-command", set_string command,
     " Executable for solver");
    ("-solver-args", set_string solver_args,
     " Extra arguments to pass wholesale to solver");
    ("-cfa", Set_int cfa,
     " k to use for k-cfa inference");
    ("-intrinsics", set_string intrinsics_file,
     " Load definitions of standard operations from <file>");
    ("-files", Rest (fun s -> file_list := s::!file_list),
     " Interpret all remaining arguments as files to test");
  ] in
  let update () = {
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
  } in
  (spec, update)

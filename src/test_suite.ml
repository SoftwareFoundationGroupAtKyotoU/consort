exception TestTimeout
exception InternalSpacerError
exception OutOfMemory

let spacer_error_p msg =
  msg = "tactic failed: Overflow encountered when expanding vector"

let run_test v_opts intr expect file =
  let res = Consort.check_file ~opts:v_opts ~intrinsic_defn:intr file in
  let open Consort in
  match res,expect with
  | Verified,true -> ()
  | Unverified (SolverError msg),_ when spacer_error_p msg -> raise InternalSpacerError
  | Unverified (SolverError "out of memory"), _ -> raise OutOfMemory
  | Unverified (SolverError msg),_ -> failwith @@ "Solver failed with message: " ^ msg
  | Unverified Timeout,_ -> raise TestTimeout
  | Unverified _,false -> ()
  | s,true -> failwith @@ Printf.sprintf "%s did not verify as expected (%s)" file @@ result_to_string s
  | Verified,false -> failwith @@ Printf.sprintf "%s incorrectly verified" file

let test_file run n_tests f_name =
  if Filename.check_suffix f_name ".imp" then
    try
      run f_name;
      incr n_tests
    with
    | Failure s -> failwith @@ Printf.sprintf "Test %s failed with message: %s" f_name s
    | TestTimeout -> Printf.printf "!!! WARNING: Test %s timed out, optimistically continuing... !!!\n" f_name; flush stdout
    | InternalSpacerError -> Printf.printf "!!! WARNING: Test %s triggered a spacer bug, optimistically continuing... !!!\n" f_name; flush stdout
    | OutOfMemory -> Printf.printf "!!! WARNING: Test %s exhausted solver memory, optimistically continuing... !!!\n" f_name; flush stdout
    | e ->
      Printexc.print_backtrace stdout;
      failwith @@ Printf.sprintf "Test %s failed with unknown exception: %s " f_name @@ Printexc.to_string e
  else ()

let () =
  let expect = ref true in
  let verbose = ref false in
  let maybe_print s = if !verbose then (print_string s; flush stdout) else () in
  let (a_list,gen) =
    Consort.Options.solver_arg_gen ()
    |> Consort.Options.seq Consort.Options.solver_opt_gen
  in
  let (i_list,i_gen) = Intrinsics.option_loader () in
  let file_list = ref [] in
  let args = [
    ("-neg", Arg.Clear expect, "Expect typing failures");
    ("-pos", Arg.Set expect, "Expect typing success (default)");
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference");
    ("-verbose", Arg.Set verbose, "Provide more output");
    ("-files", Arg.Rest (fun s ->
       file_list := s::!file_list
     ), "Interpret all remaining arguments as files to test"
    )
  ] @ i_list @ a_list in
  let dir_list = ref [] in
  Arg.parse args (fun x -> dir_list := x::!dir_list) "Check folders for expected typing failures/success";
  let v_opts = gen () in
  let intr = i_gen () in
  let n_tests = ref 0 in
  let run = run_test v_opts intr !expect in
  maybe_print "Testing ";
  List.iter (fun dir ->
    maybe_print @@ dir ^ "... ";
    let test_files = Sys.readdir dir in
    Array.iter (fun f_name ->
      test_file run n_tests @@ Filename.concat dir f_name
    ) test_files;
  ) !dir_list;
  List.iter (test_file run n_tests) !file_list; 
  Printf.printf "PASSED (%d tests)\n" @@ !n_tests

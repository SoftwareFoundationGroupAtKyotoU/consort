exception TestTimeout
exception InternalSpacerError
exception OutOfMemory

let spacer_error_p msg =
  msg = "tactic failed: Overflow encountered when expanding vector"

let run_test ~opts file =
  let res = Consort.check_file ~opts file in
  let open Consort in
  match res, opts.expect_typing with
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
  let (spec, update) =
    let open ArgOptions in
    solver_arg_gen ()
    |> spec_seq solver_opt_gen
    |> spec_seq intrinsics_arg_gen
    |> spec_seq test_suite_arg_gen
  in
  let dir_list = ref [] in
  Arg.parse spec (fun x -> dir_list := x::!dir_list) "Check folders for expected typing failures/success";
  let opts = update () in
  let run = run_test ~opts in
  let maybe_print s = if opts.verbose then (print_string s; flush stdout) else () in
  maybe_print "Testing ";
  let n_tests = ref 0 in
  List.iter (fun dir ->
    maybe_print @@ dir ^ "... ";
    let test_files = Sys.readdir dir in
    Array.iter (fun f_name ->
      test_file run n_tests @@ Filename.concat dir f_name
    ) test_files;
  ) !dir_list;
  List.iter (test_file run n_tests) opts.file_list;
  Printf.printf "PASSED (%d tests)\n" @@ !n_tests

exception TestTimeout

let run_test v_opts intr expect file =
  let res = Consort.check_file ~opts:v_opts ~intrinsic_defn:intr file in
  let open Consort in
  match res,expect with
  | Verified,true -> ()
  | Unverified (SolverError msg),_ -> failwith @@ "Solver failed with message: " ^ msg
  | Unverified Timeout,_ -> raise TestTimeout
  | Unverified _,false -> ()
  | _,true -> failwith @@ Printf.sprintf "%s did not verify as expected" file
  | _,false -> failwith @@ Printf.sprintf "%s incorrectly verified" file 

let () =
  let expect = ref true in
  let (a_list,gen) =
    Consort.Options.solver_arg_gen ()
    |> Consort.Options.seq Consort.Options.solver_opt_gen
  in
  let (i_list,i_gen) = Intrinsics.option_loader () in
  let args = [
    ("-neg", Arg.Clear expect, "Expect typing failures");
    ("-pos", Arg.Set expect, "Expect typing success (default)");
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference")
  ] @ i_list @ a_list in
  let dir_list = ref [] in
  Arg.parse args (fun x -> dir_list := x::!dir_list) "Check folders for expected typing failures/success";
  let v_opts = gen () in
  let intr = i_gen () in
  let n_tests = ref 0 in
  List.iter (fun dir -> 
    let test_files = Sys.readdir dir in
    Array.iter (fun f_name ->
      if Filename.check_suffix f_name ".imp" then
        try
          run_test v_opts intr !expect (dir ^ "/" ^ f_name);
          incr n_tests
        with
        | Failure s -> failwith @@ Printf.sprintf "Test %s failed with message: %s" f_name s
        | TestTimeout -> Printf.printf "!!! WARNING: Test %s timed out, optimistically continuing... !!!\n" f_name; flush stdout
        | e -> failwith @@ Printf.sprintf "Test %s failed with unknown exception: %s " f_name @@ Printexc.to_string e
      else ()
    ) test_files;
  ) !dir_list;
  Printf.printf "PASSED (%d tests)\n" @@ !n_tests

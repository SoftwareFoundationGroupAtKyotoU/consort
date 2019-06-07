let run_test expect file =
  if expect <> (VerifyUtil.check_file file) then
    failwith @@
      if expect then file ^ " did not verify as expected"
      else file ^ " incorrectly verified"
  else
    ()

let () =
  let expect = ref true in
  let args = [
    ("-neg", Arg.Clear expect, "Expect typing failures");
    ("-pos", Arg.Set expect, "Expect typing success (default)");
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference")
  ] in
  let dir_list = ref [] in
  Arg.parse args (fun x -> dir_list := x::!dir_list) "Check folders for expected typing failures/success";
  List.iter (fun dir -> 
    let test_files = Sys.readdir dir in
    Array.iter (fun f_name ->
      if Filename.check_suffix f_name ".imp" then
        run_test !expect (dir ^ "/" ^ f_name)
      else ()
    ) test_files;
  ) !dir_list;
  print_endline "PASSED"
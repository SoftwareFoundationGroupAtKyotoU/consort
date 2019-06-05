let run_test expect file =
  if expect <> (VerifyUtil.check_file file) then
    failwith @@
      if expect then file ^ " did not verify as expected"
      else file ^ " incorrectly verified"
  else
    ()

let () =
  let args = Sys.argv in
  if (Array.length args) < 3 then
    exit 1
  else
    let expect = Sys.argv.(1) = "--pos" in
    let dir = Sys.argv.(2) in
    let test_files = Sys.readdir dir in
    Array.iter (fun f_name ->
      if String.length f_name < 4 then
        ()
      else if 
        let last4 = String.sub f_name ((String.length f_name) - 4) 4 in
        last4 <> ".imp" then
        ()
      else
        run_test expect (dir ^ "/" ^ f_name)
    ) test_files;
    print_endline "PASSED"

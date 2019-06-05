let () =
  let in_name = Sys.argv.(1) in
  let res = VerifyUtil.check_file ~print_cons:true ~print_pred:true ~print_ast:true in_name in
  print_endline @@ if res then "VERIFIED" else "UNVERIFIED"

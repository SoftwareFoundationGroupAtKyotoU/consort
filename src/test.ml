let () =
  let in_name = Sys.argv.(1) in
  let res = VerifyUtil.check_file ~print_ast:true in_name in
  print_endline @@ if res then "VERIFIED" else "UNVERIFIED"

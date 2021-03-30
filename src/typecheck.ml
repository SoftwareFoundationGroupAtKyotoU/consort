let () =
  let n = ref None in
  let opts = ArgOptions.parse (fun s -> n := Some s) "Parse and (simple) typecheck <file>" in
  match !n with
  | None -> print_endline "No file provided"
  | Some f -> let _ = Consort.typecheck ~opts f in ()

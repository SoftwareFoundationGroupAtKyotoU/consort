let () =
  let n = ref None in
  let opts = ArgOptions.parse (fun s -> n := Some s) "Run ownership inference on <file>" in
  match !n with
  | None -> print_endline "No file provided"
  | Some f -> let _ = Consort.ownership ~opts f in ()

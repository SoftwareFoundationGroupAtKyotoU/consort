let run_with_file spec u k =
  let n = ref None in
  Arg.parse spec (fun s -> n := Some s) u;
  match !n with
  | None -> print_endline "No file provided"
  | Some s -> k s

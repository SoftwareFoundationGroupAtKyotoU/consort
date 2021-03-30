let result_to_yaml =
  let (<<) f g x = f (g x) in
  let open Consort in
  Yaml.to_string_exn <<
  function
  | Verified -> `O ["result", `Bool true]
  | Unverified r ->
    let result = ["result", `Bool false] in
    let reason = ["reason", `String (reason_to_string r false)] in
    let msg = match r with
      | UnhandledSolverOutput s
      | SolverError s -> [("msg", `String s)]
      | _ -> []
    in
    `O (result @ reason @ msg)

let result_to_exit =
  let open Consort in
  function
  | Verified -> exit 0
  | Unverified _ -> exit 1

let () =
  let target_name = ref None in
  let opts = ArgOptions.parse (fun s -> target_name := Some s) "Verify imp file" in
  match !target_name with
  | None -> print_endline "No file provided"; exit 1
  | Some file ->
    let res =
      match opts.exec_mode with
      | Consort -> Consort.consort ~opts file
      | Ownership -> Consort.ownership ~opts file
      | Typecheck -> Consort.typecheck ~opts file
    in
    if opts.yaml then
      print_endline @@ result_to_yaml res
    else
      print_endline @@ Consort.result_to_string res;
    if opts.exit_status then
      result_to_exit res
    else
      ()

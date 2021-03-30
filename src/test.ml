let result_to_yaml =
  let open Consort in
  function
  | Verified -> `O [("result", `Bool true)]
  | Unverified r ->
    let expl = match r with
      | Timeout ->
        [("reason", `String "timeout")]
      | Unsafe ->
        [("reason", `String "unsafe")]
      | UnhandledSolverOutput s ->
        [("reason", `String "unhandled"); ("msg", `String s)]
      | SolverError s ->
        [("reason", `String "solver-error"); ("msg", `String s)]
      | Aliasing ->
        [("reason", `String "ownership")]
      | Unknown ->
        [("reason", `String "unknown")] in
    `O ([("result", `Bool false)] @ expl)

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
  | Some in_name ->
    let res = Consort.check_file ~opts in_name in
    let () =
      if opts.yaml then
        print_endline @@ Yaml.to_string_exn @@ result_to_yaml res
      else
        print_endline @@ Consort.result_to_string res;
    in
    if opts.exit_status then
      result_to_exit res
    else
      ()

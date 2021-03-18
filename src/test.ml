let () =
  let (spec, to_opts) =
    let open ArgOptions in
    debug_arg_gen ()
    |> spec_seq solver_arg_gen
    |> spec_seq solver_opt_gen
    |> spec_seq intrinsics_arg_gen
    |> spec_seq test_arg_gen
  in
  let target_name = ref None in
  Arg.parse spec (fun s -> target_name := Some s) "Verify imp file";
  match !target_name with
  | None -> print_endline "No file provided"; exit 1
  | Some in_name ->
    let opts = to_opts () in
    KCFA.cfa := opts.cfa;
    let res = Consort.check_file ~opts in_name in
    let () =
      if opts.yaml then
        let yaml_repr =
          let open Consort in
          match res with
          | Verified ->
            `O [
              ("result", `Bool true)
            ]
          | Unverified r ->
            let expl = match r with
              | Timeout -> [
                  ("reason", `String "timeout")
                ]
              | Unsafe -> [ "reason", `String "unsafe" ]
              | UnhandledSolverOutput s -> [ ("reason", `String "unhandled"); ("msg", `String s) ]
              | SolverError s -> [ ("reason", `String "solver-error"); ("msg", `String s) ]
              | Aliasing -> [ ("reason", `String "ownership") ]
              | Unknown -> [ "reason", `String "unknown" ]
            in
            `O ([ "result", `Bool false ] @ expl)
        in
        print_endline @@ Yaml.to_string_exn yaml_repr
      else
        print_endline @@ Consort.result_to_string res;
    in
    if opts.exit_status then
      match res with
      | Consort.Verified -> exit 0
      | Consort.Unverified _ -> exit 1
    else
      ()

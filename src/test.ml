let () =
  let (flags,to_opts) =
    let open Consort.Options in
    let open ArgOptions in
    debug_arg_gen ()
    |> seq solver_arg_gen
    |> seq solver_opt_gen
  in
  let (intr_fl,loader) = Intrinsics.option_loader () in
  let return_status = ref false in
  let yaml_result = ref false in
  let spec = flags @ intr_fl @ [
      ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference");
      ("-exit-status", Arg.Set return_status, "Indicate successful verification with exit code");
      ("-yaml", Arg.Set yaml_result, "Print verification result in YAML format");
  ] in
  let target_name = ref None in
  Arg.parse spec (fun s -> target_name := Some s) "Verify imp file";
  match !target_name with
  | None -> print_endline "No file provided"; exit 1
  | Some in_name -> 
    let res = Consort.check_file ~opts:(to_opts()) ~intrinsic_defn:(loader ()) in_name in
    let () = 
      if !yaml_result then
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
    
    if !return_status then
      match res with
      | Consort.Verified -> exit 0
      | Consort.Unverified _ -> exit 1
    else
      ()

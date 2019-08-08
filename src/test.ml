let () =
  let (flags,to_opts) =
    let open Consort.Options in
    debug_arg_gen ()
    |> seq solver_arg_gen
    |> seq solver_opt_gen
  in
  let (intr_fl,loader) = Intrinsics.option_loader () in
  let spec = flags @ intr_fl @ [
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference");
  ] in
  let target_name = ref None in
  Arg.parse spec (fun s -> target_name := Some s) "Verify imp file";
  match !target_name with
  | None -> print_endline "No file provided"
  | Some in_name -> 
    let res = Consort.check_file ~opts:(to_opts()) ~intrinsic_defn:(loader ()) in_name
    in
    print_endline @@ Consort.result_to_string res

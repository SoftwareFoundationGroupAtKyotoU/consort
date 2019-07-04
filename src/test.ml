let () =
  let intrinsic_file = ref None in
  let (flags,to_opts) = VerifyUtil.Options.get_arg_gen () in
  let spec = let open Arg in
  flags @ [
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference");
    ("-intrinsics", String (fun x -> intrinsic_file := Some x), "Load definitions of standard operations from <file>")
  ] in
  let target_name = ref None in
  Arg.parse spec (fun s -> target_name := Some s) "Verify imp file";
  match !target_name with
  | None -> print_endline "No file provided"
  | Some in_name -> 
    let res = VerifyUtil.check_file ~opts:(to_opts()) ?intrinsic_defn:!intrinsic_file in_name
    in
    print_endline @@ if res then "VERIFIED" else "UNVERIFIED"

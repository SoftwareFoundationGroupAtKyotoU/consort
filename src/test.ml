let () =
  let show_cons = ref true in
  let show_pred = ref true in
  let show_ast = ref true in
  let show_model = ref false in
  let save_cons = ref None in
  let intrinsic_file = ref None in
  let all_debug_flags = [ show_cons; show_pred; show_ast; show_model ] in
  let spec = let open Arg in [
    ("-no-cons", Clear show_cons, "Do not print constraints sent to z3");
    ("-no-ast", Clear show_ast, "Do not print (low-level) AST");
    ("-no-pred", Clear show_pred, "Do not print predicate explanations");
    ("-show-model", Set show_model, "Print model produced from successful verification");
    ("-save-cons", String (fun r -> save_cons := Some r), "Save constraints in <file>");
    ("-show-all", Unit (fun () ->
       List.iter (fun r -> r := true) all_debug_flags
     ), "Show all debug output");
    ("-none", Unit (fun () ->
       List.iter (fun r -> r:= false) all_debug_flags
     ), "Suppress all debug output");
    ("-cfa", Arg.Set_int KCFA.cfa, "k to use for k-cfa inference");
    ("-intrinsics", String (fun x -> intrinsic_file := Some x), "Load definitions of standard operations from <file>")
  ] in
  let target_name = ref None in
  Arg.parse spec (fun s -> target_name := Some s) "Verify imp file";
  match !target_name with
  | None -> print_endline "No file provided"
  | Some in_name -> 
    let res = VerifyUtil.check_file ~print_cons:!show_cons ?save_cons:!save_cons ~print_pred:!show_pred ~print_ast:!show_ast ~get_model:!show_model ?intrinsic_defn:!intrinsic_file in_name in
    print_endline @@ if res then "VERIFIED" else "UNVERIFIED"

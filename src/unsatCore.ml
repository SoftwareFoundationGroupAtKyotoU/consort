open Sexplib.Sexp

let () =
  let buf = load_sexps Sys.argv.(1) |>
      List.filter (function
            | List [ Atom "get-model" ] -> false
            | _ -> true)
  in
  let id_counter = ref 0 in
  print_endline "(set-option :produce-unsat-cores true)";
  List.iter (fun b ->
    let b' =
      match b with
      | List [ Atom "assert"; rest ] ->
        let id = (incr id_counter; !id_counter) in
        List [
          Atom "assert";
          List [
            Atom "!";
            rest;
            Atom ":named";
            Atom (Printf.sprintf "a%d" id)
          ]
        ]
      | b -> b
    in
    to_string_hum b' |> print_endline
  ) buf;
  print_endline "(get-unsat-core)"

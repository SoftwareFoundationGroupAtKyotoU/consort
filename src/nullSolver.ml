let solve ~opts:_ ~debug_cons ?save_cons ~get_model:_ ~defn_file cons =
  let cons = SexpPrinter.to_string cons in
  let cons' =
    Option.map Files.string_of_file defn_file
    |> Option.fold ~some:(fun v ->
        v ^ cons
      ) ~none:cons
  in
  (if debug_cons then
     Printf.fprintf stderr "Generated constraints >>>\n%s\n<<<" cons';
  );
  flush stderr;
  Option.map open_out save_cons
  |> Option.map output_string
  |> Option.iter (fun f -> f cons');
  Solver.Unhandled "dummy solver"

let solve_cont ~opts:_ ~get_model:_ ~defn_file:_ _ = failwith "Unsupported"

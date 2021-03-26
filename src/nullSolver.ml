let solve ~opts cons =
  let cons = SexpPrinter.to_string cons in
  let cons' =
    Option.map Files.string_of_file (ArgOptions.get_intr opts).def_file
    |> Option.fold ~some:(fun v ->
        v ^ cons
      ) ~none:cons
  in
  (if opts.ArgOptions.debug_cons then
     Printf.fprintf stderr "Generated constraints >>>\n%s\n<<<" cons';
  );
  flush stderr;
  Option.map open_out opts.ArgOptions.save_cons
  |> Option.map output_string
  |> Option.iter (fun f -> f cons');
  Solver.Unhandled "dummy solver"

let solve_cont ~opts:_ _ = failwith "Unsupported"

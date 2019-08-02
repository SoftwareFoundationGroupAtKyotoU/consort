module Backend = SmtLibBackend.Make(struct
    let ownership_ante = Z3BasedBackend.ownership_ante
    let ownership r =
      OwnershipSolver.print_ownership_constraints
        r.Inference.Result.ovars
        r.Inference.Result.ownership

    let solve ~opts:_ ~debug_cons ?save_cons ~get_model:_ ~defn_file cons =
      let cons = SexpPrinter.to_string cons in
      let cons' =
        Std.Option.map Files.string_of_file defn_file
        |> Std.Option.fold ~f:(fun acc v ->
              v ^ acc
          ) ~acc:cons
      in
      (if debug_cons then
         Printf.fprintf stderr "Generated constraints >>>\n%s\n<<<" cons';
      );
      flush stderr;
      Std.Option.map open_out save_cons
      |> Std.Option.map output_string
      |> Std.Option.iter (fun f -> f cons');
      Solver.Unhandled "null"
  end)

let solve = Backend.solve

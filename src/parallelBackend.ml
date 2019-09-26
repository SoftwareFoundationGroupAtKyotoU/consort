module type S = sig
  val solve_cont : opts:Solver.options -> get_model:bool -> defn_file:(string option) -> SexpPrinter.t -> Solver.cont
end

let backends = [
  (module HornBackend.Backend : S);
  (module HoiceBackend.Backend : S);
  (module SmtBackend.Backend : S)
  
]

module Backend = SmtLibBackend.Make(struct  
    let solve ~opts ~debug_cons:_ ?save_cons:_ ~get_model ~defn_file cons =
      let proc_pool =
        List.map (fun d ->
          let module D = (val d : S) in
          D.solve_cont ~opts ~get_model ~defn_file cons
        ) backends
      in
      Process.select_pool ~timeout:(opts.Solver.timeout + 10) ~prock:(fun acc res ->
        match res with
        | Solver.Sat _ | Solver.Unsat -> `Return res
        | _ -> `Continue (res::acc)
      ) ~acc:[] ~finish:(fun l ->
        assert (l <> []);
        List.hd l
      ) proc_pool
  end)

let solve = Backend.solve

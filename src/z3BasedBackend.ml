module type STRATEGY = sig
  val ownership: Inference.funenv -> int list -> Inference.ocon list -> SexpPrinter.t -> unit
  val z3_tactic : string
end

module Make(S: STRATEGY) = struct
  open SexpPrinter
  open Inference

  include SmtLibBackend.Make(struct
      let ownership = S.ownership
          
      let po = OwnershipSolver.po

      let rec ownership_ante =
        let rel = function
          | `Ge -> ">="
          | `Gt -> ">"
          | `Eq -> "="
        in
        function
        | ORel (o,c,f) ->
          pg (rel c) [
              po o;
              plift @@ string_of_float f
            ]
        | OAny ol ->
          pg "or" @@ List.map ownership_ante ol

      let solve = Z3Channel.call_z3 ~strat:S.z3_tactic
    end)
end

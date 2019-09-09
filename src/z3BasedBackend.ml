module type STRATEGY = sig
  val z3_tactic : string
end

module Make(S: STRATEGY) = struct
  include SmtLibBackend.Make(struct
      let solve = Z3Channel.call_z3 ~strat:S.z3_tactic
    end)
end

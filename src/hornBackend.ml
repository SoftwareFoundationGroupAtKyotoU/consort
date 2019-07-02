let pred = "(define-fun ov-wf ((o Real) (m Int)) Bool
  (and (<= o 1) (<= 0 o) (= o (* 0.05 m))))"

module HornStrategy(I: Z3BasedBackend.OV) = struct
  module M = SmtBackend.SMTStrategy(I)
  open SexpPrinter
  open RefinementTypes

  let mult_name i =
    (I.ovar_name i) ^ "-mult"

  let pp_wf o_buf i =
    pg "assert" [
      pg "ov-wf" [
        pl @@ I.ovar_name i;
        pl @@ mult_name i
      ]
    ] o_buf;
    break o_buf

  let rec collect_ovars acc = function
    | Ref (t,OVar o) -> (collect_ovars ((plift @@ I.ovar_name o)::acc) t)
    | Ref (t,_) -> collect_ovars acc t
    | Int _ -> acc
    | Tuple (_,t) -> List.fold_left collect_ovars acc t

  let ownership theta ovars ocons ff =
    let o_buf = SexpPrinter.fresh () in
    M.ownership theta ovars ocons o_buf;
    atom o_buf pred;
    break o_buf;
    let i = StringMap.fold (fun _ { arg_types; _ } acc ->
        List.fold_left collect_ovars acc arg_types
      ) theta []
    in
    if (List.length i > 0) then begin
      pg "minimize" [
        pg "+" i
      ] o_buf
    end;
    List.iter (fun i ->
      pg "declare-const" [
        pl @@ mult_name i;
        pl "Int"
      ] o_buf;
      break o_buf
    ) ovars;
    List.iter (pp_wf o_buf) ovars;
    finish o_buf;
    let (res,model) = Z3Channel.call_z3_raw ~debug_cons:false ~defn_file:None ~strat:"(check-sat)" o_buf in
    match res,model with
    | "sat",Some m -> begin
      let open Sexplib.Sexp in
      let s = scan_sexp @@ Lexing.from_string m in
      match s with
      | List (Atom "model"::model) ->
        List.iter (fun l ->
            atom ff (to_string_hum l);
            break ff
          ) model
      | _ -> raise Z3BasedBackend.OwnershipFailure
      end
    | _ -> raise Z3BasedBackend.OwnershipFailure

  include Z3BasedBackend.StandardSolver(struct
      let strat = "(check-sat-using (then qe-light horn))"
    end)
end

module Backend = Z3BasedBackend.Make(HornStrategy)

let solve = Backend.solve

exception OwnershipFailure

module type STRATEGY = sig
  val ownership: Inference.funenv -> int list -> Inference.ocon list -> SexpPrinter.t -> unit
  val solve: debug_cons:bool -> ?save_cons:string -> get_model:bool -> defn_file:(string option) -> SexpPrinter.t -> Prover.result
  val ownership_ante : Inference.oante -> (Sexplib.Sexp.t -> 'a) -> 'a
end

type intrinsic_interp  = (string StringMap.t) * string option

module Make(S: STRATEGY) : sig
  val solve : debug_cons:bool ->  ?save_cons:string -> get_model:bool -> interp:intrinsic_interp -> Inference.Result.t -> Prover.result
end = struct
  open SexpPrinter
  open Inference
  open RefinementTypes

  let pred_name p = p
    
  let pp_imm o ff = match o with
    | RAp ap -> atom ff @@ Paths.to_z3_ident ap
    | RConst i -> atom ff @@ string_of_int i

  let pp_relop binding r ff = match r with
    | Nu -> atom ff binding
    | RImm ri -> pp_imm ri ff

  let refine_args o l =
    List.filter ((<>) o) l
    |> List.map Paths.to_z3_ident

  let ctxt_var i = "CTXT" ^ (string_of_int i)

  let string_of_nullity = function
    | `NNull -> "false"
    | `NLive -> "true"
    | `NVar v -> v

  let rec pp_refine ~nullity ~interp r (binding_ap: Paths.concr_ap) ff =
    let binding = Paths.to_z3_ident binding_ap in
    match r with
    | NamedPred (n,(args,o)) ->
      ff |> psl @@ [ n; binding ] @ (refine_args o args)
    | Pred (i,(args,o)) ->
      let ctxt = List.init !KCFA.cfa ctxt_var in
      print_string_list (pred_name i::ctxt @ [ binding ] @ (refine_args o args) @ [ string_of_nullity nullity ]) ff
    | CtxtPred (ctxt,i,(args,o)) ->
      let c_string = (string_of_int ctxt)::(List.init (!KCFA.cfa-1) (fun i -> ctxt_var @@ i + 1)) in
      print_string_list (pred_name i::c_string @ [ binding ] @ (refine_args o args) @ [ string_of_nullity nullity ]) ff
    | Top -> atom ff "true"
    | ConstEq n -> print_string_list [ "="; binding; string_of_int n ] ff
    | Relation { rel_op1; rel_cond = cond_name; rel_op2 } ->
      let intr = StringMap.find cond_name interp in
      pg intr [
        pp_relop binding rel_op1;
        pp_imm rel_op2
      ] ff
    | And (r1,r2) ->
      pg "and" [
          pp_refine ~nullity ~interp r1 binding_ap;
          pp_refine ~nullity ~interp r2 binding_ap
        ] ff

  let pp_owner_ante = S.ownership_ante

  let close_env env _ _ =
    (* this is a cheap hack to get our current tests to pass *)
    (* TODO: do this properly ... *)
    List.filter (fun (k,_,_) ->
      match k with
      | `ADeref _ -> false
      | _ -> true
    ) env

  let simplify sexpr =
    let open Sexplib.Sexp in
    (fun k ->
      let rec simplify_loop acc r =
        match r with
        | List (Atom "and"::rest) ->
          List.fold_left simplify_loop acc rest
        | Atom "true" -> acc
        | _ -> r::acc
      in
      match simplify_loop [] sexpr with
      | [] -> k @@ Atom "true"
      | [h] -> k h
      | l -> k @@ List (Atom "and"::l)
    )

  let map_nullity (c,n_acc) n =
    match n with
    | `NUnk ->
      let id = Printf.sprintf "null?%d" c in
      `NVar id,(c+1,id::n_acc)
    | `NNull -> `NNull,(c,n_acc)
    | `NLive -> `NLive,(c,n_acc)
      
  let pp_constraint ~interp ff { env; ante; conseq; owner_ante; nullity } =
    let gamma = close_env env ante conseq in
    let context_vars = List.init !KCFA.cfa (fun i -> Printf.sprintf "(%s Int)" @@ ctxt_var i) in
    let env_vars = List.map (fun (ap,_,_) -> Printf.sprintf "(%s Int)" @@ Paths.to_z3_ident ap) gamma in
    let free_vars = "(NU Int)":: context_vars @ env_vars in
    let n_acc,denote_gamma = Std.double_fold (fun n_acc acc (ap,r,n) ->
        let pp_null,nacc' = map_nullity n_acc n in
        nacc',pp_refine ~nullity:pp_null ~interp r ap::acc
      ) gamma (0,[]) [] in
    let cons_null,(_,b_vars) = map_nullity n_acc nullity in
    let null_args = List.map (Printf.sprintf "(%s Bool)") b_vars in
    let oante = List.map pp_owner_ante owner_ante in
    let e_assum = oante @ denote_gamma in
    pg "assert" [
      pg "forall" [
        print_string_list (free_vars @ null_args);
        pg "=>" [
          pg "and" ((pp_refine ~nullity:cons_null ~interp ante (`AVar "NU"))::e_assum) simplify;
          pp_refine ~nullity:cons_null ~interp conseq (`AVar "NU")
        ]
      ]
    ] ff.printer;
    break ff

  let solve ~debug_cons ?save_cons ~get_model ~interp:(interp,defn_file) infer_res =
    let ff = SexpPrinter.fresh () in
    let open Inference.Result in
    let { ownership = owner_cons; ovars; refinements; arity; theta; _ } = infer_res in
    StringMap.iter (fun k v ->
      pg "declare-fun" [
        pl @@ pred_name k;
        psl @@ (List.init v (fun _ -> "Int")) @ [ "Bool" ];
        pl "Bool";
      ] ff.printer;
      break ff
    ) arity;
    try
      S.ownership theta ovars owner_cons ff;
      List.iter (pp_constraint ~interp ff) refinements;
      SexpPrinter.finish ff;
      S.solve ~debug_cons ?save_cons ~get_model ~defn_file ff
    with
      OwnershipFailure -> Unsat
end

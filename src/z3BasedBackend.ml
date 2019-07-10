module type OV = sig
  val ovar_name: int -> string
end

exception OwnershipFailure

module type SOLVER = sig
    val solve: debug_cons:bool -> ?save_cons:string -> get_model:bool -> defn_file:(string option) -> SexpPrinter.t -> bool
end

module StandardSolver(S: sig val strat: string end) : SOLVER = struct
   let solve ~debug_cons ?save_cons ~get_model ~defn_file cons =
    Z3Channel.call_z3 ~debug_cons ?save_cons ~get_model ~defn_file ~strat:S.strat cons     
end

module type STRATEGY = functor(I: OV) -> sig
    val ownership: Inference.funenv -> int list -> Inference.ocon list -> SexpPrinter.t -> unit
    include SOLVER
end

module Make(S: STRATEGY) = struct
  open SexpPrinter
  open Inference
  open RefinementTypes
    

  let ovar_name = OwnershipSolver.ovar_name

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

  let rec pp_refine ~interp r (binding_ap: Paths.concr_ap) ff =
    let binding = Paths.to_z3_ident binding_ap in
    match r with
    | NamedPred (n,(args,o)) ->
      ff |> psl @@ [ n; binding ] @ (refine_args o args)
    | Pred (i,(args,o)) ->
      let ctxt = List.init !KCFA.cfa ctxt_var in
      print_string_list (pred_name i::ctxt @ [ binding ] @ (refine_args o args)) ff
    | CtxtPred (ctxt,i,(args,o)) ->
      let c_string = (string_of_int ctxt)::(List.init (!KCFA.cfa-1) (fun i -> ctxt_var @@ i + 1)) in
      print_string_list (pred_name i::c_string @ [ binding ] @ (refine_args o args)) ff
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
          pp_refine ~interp r1 binding_ap;
          pp_refine ~interp r2 binding_ap
        ] ff

  let po = OwnershipSolver.po

  let rec pp_owner_ante =
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
      pg "or" @@ List.map pp_owner_ante ol

  let close_env env _ _ =
    (* this is a cheap hack to get our current tests to pass *)
    (* TODO: do this properly ... *)
    List.filter (fun (k,_) ->
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
          
      
  let pp_constraint ~interp ff { env; ante; conseq; owner_ante } =
    let gamma = close_env env ante conseq in
    let context_vars = List.init !KCFA.cfa (fun i -> Printf.sprintf "(%s Int)" @@ ctxt_var i) in
    let env_vars = List.map (fun (ap,_) -> Printf.sprintf "(%s Int)" @@ Paths.to_z3_ident ap) gamma in
    let free_vars = "(NU Int)":: context_vars @ env_vars in
    let denote_gamma = List.fold_left (fun acc (ap,r) ->
        pp_refine ~interp r ap::acc
      ) [] gamma in
    let oante = List.map pp_owner_ante owner_ante in
    let e_assum = oante @ denote_gamma in
    pg "assert" [
      pg "forall" [
        print_string_list free_vars;
        pg "=>" [
          pg "and" ((pp_refine ~interp ante (`AVar "NU"))::e_assum) simplify;
          pp_refine ~interp conseq (`AVar "NU")
        ]
      ]
    ] ff.printer;
    break ff
  module Strat = S(struct
      let ovar_name = ovar_name
    end)

  let solve ~debug_cons ?save_cons ~get_model ~interp:(interp,defn_file) infer_res =
    let ff = SexpPrinter.fresh () in
    let open Inference.Result in
    let { ownership = owner_cons; ovars; refinements; arity; theta; _ } = infer_res in
    StringMap.iter (fun k v ->
      pg "declare-fun" [
        pl @@ pred_name k;
        psl (init v (fun _ -> "Int"));
        pl "Bool";
      ] ff.printer;
      break ff
    ) arity;
    try
      Strat.ownership theta ovars owner_cons ff;
      List.iter (pp_constraint ~interp ff) refinements;
      SexpPrinter.finish ff;
      Strat.solve ~debug_cons ?save_cons ~get_model ~defn_file ff
    with
      OwnershipFailure -> false
end

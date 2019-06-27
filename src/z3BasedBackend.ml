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
    

  let ovar_name ovar = Printf.sprintf "ovar-%d" ovar

  let pred_name p = Printf.sprintf "pred-%d" p
    
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
      let ctxt = init !KCFA.cfa ctxt_var in
      print_string_list (pred_name i::ctxt @ [ binding ] @ (refine_args o args)) ff
    | CtxtPred (ctxt,i,(args,o)) ->
      let c_string = (string_of_int ctxt)::(init (!KCFA.cfa-1) (fun i -> ctxt_var @@ i + 1)) in
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

  let po = function
    | OVar o -> pl @@ ovar_name o
    | OConst f -> pl @@ string_of_float f

  let pp_owner_ante (o,c,f) =
    let rel = match c with
      | `Ge -> ">="
      | `Gt -> ">"
      | `Eq -> "="
    in
    pg rel [
      po o;
      plift @@ string_of_float f
    ]

  module APSet = Set.Make(struct type t = Paths.concr_ap let compare = Pervasives.compare end)

  let close_env env _ _ =
    (* this is a cheap hack to get our current tests to pass *)
    (* TODO: do this properly ... *)
    List.filter (fun (k,_) ->
      match k with
      | `ADeref _ -> false
      | _ -> true
    ) env
      
  let pp_constraint ~interp ff { env; ante; conseq; owner_ante } =
    let gamma = close_env env ante conseq in
    let context_vars = init !KCFA.cfa (fun i -> Printf.sprintf "(%s Int)" @@ ctxt_var i) in
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
          pg "and" ((pp_refine ~interp ante (`AVar "NU"))::e_assum);
          pp_refine ~interp conseq (`AVar "NU")
        ]
      ]
    ] ff;
    break ff

  let pp_oconstraint ff ocon =
    begin
      match ocon with
      | Write o -> pg "assert" [
                       pg "=" [
                         po o;
                         plift "1.0"
                       ]
                     ] ff
      | Live o -> pg "assert" [
                      pg ">" [
                        po o;
                        plift "0.0"
                      ]
                    ] ff
      | Shuff ((o1,o2),(o1',o2')) ->
        pg "assert" [
            pg "=" [
              pg "+" [
                po o1;
                po o2
              ];
              pg "+" [
                po o1';
                po o2'
              ];
            ]
          ] ff
      | Split (o,(o1,o2)) ->
        pg "assert" [
            pg "=" [
              po o;
              pg "+" [
                po o1;
                po o2
              ]
            ]
          ] ff
      | Eq (o1,o2) ->
        pg "assert" [
            pg "=" [
              po o1;
              po o2
            ]
          ] ff
    end;
    break ff

  module Strat = S(struct
      let ovar_name = ovar_name
    end)

  let solve ~debug_cons ?save_cons ~get_model ~interp:(interp,defn_file) infer_res =
    let ff = SexpPrinter.fresh () in
    let open Inference.Result in
    let { ownership = owner_cons; ovars; refinements; arity; theta } = infer_res in
    IntMap.iter (fun k v ->
      pp_sexpr (fun spc ps ->
        ps "declare-fun"; spc ();
        ps @@ pred_name k; spc();
        psl (init v (fun _ -> "Int")) ff;
        spc ();
        ps "Bool"
      ) ff;
      break ff
    ) arity;
    try
      Strat.ownership theta ovars owner_cons ff;
      List.iter (pp_constraint ~interp ff) refinements;
      Strat.solve ~debug_cons ?save_cons ~get_model ~defn_file ff
    with
      OwnershipFailure -> false
end

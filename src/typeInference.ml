
module Make(S: Solver.SOLVER_BACKEND) = struct
  open SexpPrinter
  open Inference
  open RefinementTypes
  open Std.StateMonad
  open Std

  type t = Inference.Result.t

  let pred_name p = p

  let pp_int i =
    if i < 0 then
      pg "-" [
       pl @@ string_of_int @@ ~- i
      ]
    else
      pl @@ string_of_int i
        

  let pp_imm o ff = match o with
    | RAp ap -> atom ff @@ Paths.to_z3_ident ap
    | RConst i -> pp_int i ff

  let pp_relop ?nu r ff = match nu,r with
    | Some binding,Nu -> atom ff binding
    | _,RImm ri -> pp_imm ri ff
    | None,_ -> failwith "Malformed constraint: did not bind a target for nu"

  let refine_args _ l = List.map Paths.to_z3_ident l

  let ctxt_var i = "CTXT" ^ (string_of_int i)

  let string_of_nullity = function
    | `NNull -> "false"
    | `NLive -> "true"
    | `NVar v -> v

  let rec pp_refine ~bif_inliner ~nullity ~interp ?nu r (ff : Sexplib.Sexp.t -> 'a) =
    let binding_opt = Option.map Paths.to_z3_ident nu in
    match binding_opt,r with
    | Some binding,NamedPred (n,(args,o)) ->
      bif_inliner ~bif:n (binding :: (refine_args o args)) ff
    | Some binding,Pred (i,(args,o)) ->
      let ctxt = List.init !KCFA.cfa ctxt_var in
      print_string_list (pred_name i::ctxt @ [ binding ] @ (refine_args o args) @ [ string_of_nullity nullity ]) ff
    | Some binding,CtxtPred (ctxt,i,(args,o)) ->
      let c_string =
        if !KCFA.cfa > 0 then
          (string_of_int ctxt)::(List.init (!KCFA.cfa-1) (fun i -> ctxt_var @@ i))
        else
          []
      in
      print_string_list (pred_name i::c_string @ [ binding ] @ (refine_args o args) @ [ string_of_nullity nullity ]) ff
    | _,Top -> atom ff "true"
    | Some binding,ConstEq n ->
      pg "=" [
          pl binding;
          pp_int n
        ] ff
    | _,Relation { rel_op1; rel_cond = cond_name; rel_op2 } ->
      let intr = StringMap.find cond_name interp in
      pg intr [
        pp_relop ?nu:binding_opt rel_op1;
        pp_imm rel_op2
      ] ff
    | _,And (r1,r2) ->
      pg "and" [
          pp_refine ~bif_inliner ~nullity ~interp ?nu r1;
          pp_refine ~bif_inliner ~nullity ~interp ?nu r2
        ] ff
    | None,(CtxtPred _ | NamedPred _ | Pred _ | ConstEq _) ->
      failwith "Malformed refinement: expect a nu binder but none was provided"
        
  let close_env env ante conseq =
    let module SS = Std.StringSet in
    let update acc =
      fold_refinement_args ~rel_arg:(fun ss a ->
        SS.add (Paths.to_z3_ident a) ss
      ) ~pred_arg:(fun acc (a,_) ->
        List.fold_left (fun acc p ->
          SS.add (Paths.to_z3_ident p) acc
        ) acc a
      ) acc
    in
    let const_paths = List.fold_left (fun acc (p,_,_) ->
        if Paths.is_const_ap p then
          SS.add (Paths.to_z3_ident p) acc
        else acc) SS.empty env
    in
    let seed = update (update const_paths ante) conseq in
    let rec fixpoint acc =
      let acc' = List.fold_left (fun acc (a,p,_) ->
          let id = Paths.to_z3_ident a in
          if SS.mem id acc then
            update acc p
          else
            acc
        ) acc env in
      if (SS.cardinal acc) = (SS.cardinal acc') then
        acc'
      else
        fixpoint acc'
    in
    let closed_names = fixpoint seed in
    List.filter (fun (k,_,_) ->
      SS.mem (Paths.to_z3_ident k) closed_names
    ) env
      
  let propagate_const assum =
    let open Sexplib.Sexp in
    let inline = List.fold_left (fun acc eq ->
        match eq with
        | List [ Atom "="; Atom nm; Atom eq ] ->
          begin
            try
              let _ = int_of_string eq in
              StringMap.add nm eq acc
            with _ -> acc
          end
        | _ -> acc
      ) StringMap.empty assum
    in
    let rec propagate expr =
      match expr with
      | Atom nm when StringMap.mem nm inline ->
        Atom (StringMap.find nm inline)
      | Atom _ -> expr
      | List l -> List (List.map propagate l)
    in
    List.map (fun expr ->
      match expr with
      | List (Atom "="::(Atom nm)::_) when StringMap.mem nm inline -> expr
      | _ -> propagate expr
    ) assum

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
      match simplify_loop [] sexpr |> propagate_const with
      | [] -> k @@ Atom "true"
      | [h] -> k h
      | l -> k @@ List (Atom "and"::l)
    )

  let to_atomic_preds =
    let rec loop acc = function
      | And (r1,r2) -> loop (loop acc r1) r2
      | r -> r::acc
    in
    loop []

  type smt_nullity = [
    | `NVar of string
    | `NLive
    | `NNull
  ]

  module NullityOrd = struct
    type key = smt_nullity
    type t = key
    let compare = compare
  end

  module NullityMap = Map.Make(NullityOrd)
  module NullitySet = Set.Make(NullityOrd)

  let lift_nullity = function
    | `NLive -> return `NLive
    | `NNull -> return @@ `NNull
    | `NVar i ->
      let nm = Printf.sprintf "bool?%d" i in
      let%bind () = mutate @@ (fun (im,vs) -> (im,StringSet.add nm vs)) in
      return @@ `NVar nm

  let lift_nullity_chain nl =
    match nl with
    | [] -> return @@ `NLive
    | [h] -> lift_nullity h
    | h::t ->
      let%bind lh = lift_nullity h in
      let rec impl_loop curr rem =
        match rem with
        | [] -> return lh
        | h'::t ->
          let%bind lh' = lift_nullity h' in
          let%bind () = mutate @@ (fun (impl,vs) ->
              let impl' = NullityMap.update curr (function
              | None -> Some (NullitySet.singleton lh')
              | Some s -> Some (NullitySet.add lh' s)
                ) impl
              in
              (impl',vs)
            ) in
          impl_loop lh' t
      in
      impl_loop lh t

  let pp_constraint bif_inliner ~interp ff { env; ante; conseq; nullity; target } =     
    let gamma = close_env env ante conseq in
    let context_vars = List.init !KCFA.cfa (fun i -> Printf.sprintf "(%s Int)" @@ ctxt_var i) in
    let env_vars =
      List.fold_left (fun acc (ap,_,_) -> StringSet.add (Paths.to_z3_ident ap) acc) StringSet.empty gamma
      |> Option.fold ~none:(Fun.id) ~some:(fun p -> StringSet.add (Paths.to_z3_ident p)) target
    in
    do_with_context (NullityMap.empty,StringSet.empty) @@
      let%bind denote_gamma = mmap (fun (p,r,nl) ->
          let%bind n' = lift_nullity_chain nl in
          return @@ pp_refine ~bif_inliner ~nullity:n' ~nu:p ~interp r
        ) gamma
      in
      let%bind pred_nullity = lift_nullity_chain nullity in
      let%bind (nullity_ante,b_vars) = get_state in
      let null_args = List.map (Printf.sprintf "(%s Bool)") @@ StringSet.elements b_vars in
      
      let nullity_assume =
        NullityMap.fold (fun src dst_set acc1 ->
          NullitySet.fold (fun dst acc2 ->
            (pg "=>" [
               pl @@ string_of_nullity src;
               pl @@ string_of_nullity dst
             ])::acc2
          ) dst_set acc1
        ) nullity_ante [] in
      let e_assum = nullity_assume @ denote_gamma in
      let free_vars = StringSet.fold (fun nm acc ->
          (Printf.sprintf "(%s Int)" nm)::acc
        ) env_vars @@ context_vars @ null_args
      in
      let atomic_preds = to_atomic_preds conseq in
      return @@ List.iter (fun atomic_conseq ->
          let precond = pg "and" ((pp_refine ~bif_inliner ~nullity:pred_nullity ~interp ?nu:target ante)::e_assum) simplify in
          pg "assert" [
            pg "forall" [
              print_string_list free_vars;
              pg "=>" [
                precond;
                pp_refine ~bif_inliner ~nullity:pred_nullity ~interp ?nu:target atomic_conseq (fun k -> fun ff -> ff k)
              ]
            ]
          ] ff.printer;
          break ff
        ) atomic_preds

  let create_inliner defns =
    let open Sexplib.Sexp in
    let module Result = Stdlib.Result in
    let subst =
      List.fold_left (fun acc defn ->
        match defn with
        | List [ Atom "define-fun"; Atom nm; List args; Atom "Bool"; body ] ->
          let arg_names_r = List.fold_left (fun acc arg_sexp ->
              match arg_sexp with
              | List [ Atom nm; Atom "Int" ] -> Result.map (List.cons nm) acc
              | _ -> Result.error ()
            ) (Result.ok []) args in
          begin
            match arg_names_r with
            | Result.Error () -> acc
            | Result.Ok nm_rev ->
              let names = List.rev nm_rev in
              StringMap.add nm (names,body) acc
          end
        | _ -> acc
      ) StringMap.empty defns
    in
    fun ~bif args ff ->
      if StringMap.mem bif subst then
        let (arg_names,body) = StringMap.find bif subst in
        assert ((List.length arg_names) = (List.length args));
        let sigma =
          List.fold_left2 (fun acc formal actual ->
            StringMap.add formal actual acc
          ) StringMap.empty arg_names args
        in
        let rec apply = function
          | Atom nm when StringMap.mem nm sigma ->
            Atom (StringMap.find nm sigma)
          | Atom a -> Atom a
          | List l -> List (List.map apply l)
        in
        ff @@ apply body
      else
        psl (bif::args) ff


  let solve_inf ~interp:(interp,defn_file) infer_res =
    let ff = SexpPrinter.fresh () in
    let open Inference.Result in
    let { refinements; arity; _ } = infer_res in
    let bif_inliner =
      match defn_file with
      | None -> fun ~bif args ->
        psl @@ bif::args
      | Some file ->
        let s_channel = open_in file in
        let defns = Sexplib.Sexp.input_sexps s_channel in
        close_in s_channel;
        create_inliner defns
    in
    StringMap.iter (fun k (ground,v) ->
      pg "declare-fun" [
        pl @@ pred_name k;
        psl @@ (List.init v (fun _ -> "Int")) @ [ "Bool" ];
        pl "Bool";
      ] ff.printer;
      break ff;
      begin
        if ground then
          let g_name = Printf.sprintf "!g%d" in
          pg "assert" [
            pg "forall" [
              ll @@ List.init v (fun i -> psl [ g_name i; "Int"]);
              pg (pred_name k) @@ (List.init v (fun i -> pl @@ g_name i)) @ [
                pl "false"
              ]
            ]
          ] ff.printer;
          break ff
          
      end;
    ) arity;
    List.iter (pp_constraint bif_inliner ~interp ff) refinements;
    SexpPrinter.finish ff;
    S.solve ~defn_file ff

  let pprint_ty_env =
    let open PrettyPrint in
    fun ty_envs (i,_) _ ->
      let ty_env = Hashtbl.find ty_envs i in
      if (StringMap.cardinal ty_env) = 0 then
        pl [ ps "/* empty */"; newline ]
      else
        let pp_ty_env = StringMap.bindings ty_env
          |> List.map (fun (k,t) ->
              pb [
                pf "%s: " k;
                RefinementTypes.pp_type t
              ]
            )
          |> psep_gen newline
        in
        pblock ~nl:true ~op:(ps "/*") ~body:pp_ty_env ~close:(ps "*/")
    
  let solve ~annot_infr ~dump_ir:_ ~intr simple_res o_hints ast =
    let res = infer
        ~save_types:true
        ~intrinsics:intr.Intrinsics.op_interp
        simple_res o_hints ast
    in
    let () =
      if annot_infr then
        let ty_envs = res.Result.ty_envs in
        AstPrinter.pretty_print_program ~with_labels:true ~annot:(pprint_ty_env ty_envs) stderr ast;
        flush stderr
    in
    let answer = solve_inf ~interp:(intr.Intrinsics.rel_interp,intr.Intrinsics.def_file) res in
    (res,answer)

end

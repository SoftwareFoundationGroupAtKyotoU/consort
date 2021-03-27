
(* TODO: factor this out better *)
module Make(C : Solver.SOLVER_BACKEND) = struct
  type t = unit
  open SexpPrinter
  open FlowInference
  open Std.StateMonad

  include (val Log.located ~where:"FB")

  module RT = RefinementTypes

  let pp_ap p = pl @@ Paths.to_z3_ident p

  let pp_ztype = function
    | ZInt -> pl "Int"
    | ZBool -> pl "Bool"

  let pp_imm = function
    | Ap p -> pl @@ Paths.to_z3_ident p
    | IConst i -> pl @@ string_of_int i
    | BConst b -> pl @@ Bool.to_string b
    | _ -> assert false

  let add_ident path ty map =
    (Paths.PathMap.update path (function
     | None -> Some ty
     | Some ty' -> if ty' <> ty then failwith @@ Printf.sprintf "Something has gone wrong for path %s" (Paths.to_z3_ident path) else Some ty'
     ) map),()

  let context_at = Printf.sprintf "ctxt$%d"

  let choice_counter = ref 0

  let pp_int i =
    if i < 0 then
      ll [ pl "-"; pl @@ string_of_int @@ ~-i ]
    else
      pl @@ string_of_int i
     

  let close_and_print ~opts ~fgen clause =
    let rel_op = (ArgOptions.get_intr opts).rel_interp in
    let rec pp_arg ty = function
      | Ap p -> add_ident p ty >> return @@ pp_ap p
      | IConst i -> return @@ pp_int i
      | BConst b -> return @@ pl @@ Bool.to_string b
      | KeyedChoice (b,a1,a2) ->
        let%bind a1_pp = pp_arg ty a1 in
        let%bind a2_pp = pp_arg ty a2 in
        add_ident b ZBool >>
        return @@ pg "ite" [
            pp_ap b;
            a1_pp;
            a2_pp
          ]
    in
    match clause with
    | Relation (p,ty) ->
      let%bind p1 = pp_arg ty p.rel_op1 in
      let%bind p2 = pp_arg ty p.rel_op2 in
      return RefinementTypes.(
          let rel_sym = StringMap.find p.rel_cond rel_op in
          pg rel_sym [
            p1;
            p2
          ]
        )
    | NamedRel (name,args) ->
      miter (function
        | Ap p -> add_ident p ZInt
        | _ -> return ()
        ) args >>
      return @@ pg name @@ List.map pp_imm args
    | NullCons (p1,p2) ->
      let%bind p1 = pp_arg ZBool p1 in
      let%bind p2 = pp_arg ZBool p2 in
      return @@ pg "=>" [
          p1;
          p2
        ]

    | PRelation ((name,formals,_),subst,ctxt_shift) ->
      let pred = fgen name in
      let subst_map = List.fold_left (fun acc (k,v) ->
          Paths.PathMap.add k v acc
        ) Paths.PathMap.empty subst
      in
      let%bind val_args =
        mmap (fun (arg_path,ty) ->
          if pred arg_path then
            let subst = Paths.PathMap.find_opt arg_path subst_map in
            match subst with
            | None -> add_ident arg_path ty >> return @@ Some (pp_ap arg_path)
            | Some subst -> let%bind a = pp_arg ty subst in return (Some a)
          else
            return None
        ) formals
      in
      let val_args = List.filter_map Fun.id val_args in
      let%bind ctxt_args =
        if opts.cfa = 0 then
          return []
        else
          let tl_adj = Option.fold ~none:0 ~some:(Fun.const 1) ctxt_shift in
          let%bind tail = List.init (opts.cfa - tl_adj) context_at |> List.map P.var |> mmap (fun ap ->
                add_ident ap ZInt >> return @@ pp_ap ap
              ) in
          match ctxt_shift with
          | None -> return tail
          | Some i -> return @@ (pl @@ string_of_int i)::tail
      in
      let args = ctxt_args @ val_args in
      if (List.compare_length_with args 0) > 0 then
        return @@ pg name args
      else
        return @@ pl name

  let close_impl ~opts ~fgen ante conseq =
    let path_types = Paths.PathMap.empty in
    let path_types,ante_k = mmap (close_and_print ~opts ~fgen) ante path_types in
    let ante_k = match ante_k with
      | [] -> pl "true"
      | _ -> pg "and" ante_k
    in
    let path_types,conseq_k = close_and_print ~opts ~fgen conseq path_types in
    (path_types,ante_k,conseq_k)

  let pp_impl ~opts ~fgen (ante,conseq) ff =
    let (args,ante_k,conseq_k) = close_impl ~opts ~fgen ante conseq in
    let quantif = Paths.PathMap.bindings args |> List.map (fun (s,t) ->
        ll [ pp_ap s; pp_ztype t ]
        ) in
    if (List.compare_length_with quantif 0) > 0 then
      pg "assert" [
        pg "forall" [
          ll quantif;
          pg "=>" [
            ante_k;
            conseq_k
          ]
        ]
      ] ff.printer
    else
      pg "assert" [
        pg "=>" [
          ante_k;
          conseq_k
        ]
      ] ff.printer

  let solve_constraints ~opts ~fgen rel impl start_relation =
    let ff = SexpPrinter.fresh () in
    let cfa = opts.ArgOptions.cfa in
    let ctxt_args = List.init cfa (fun _ -> pp_ztype ZInt) in
    let grounded =
      if cfa = 0 then
        pl start_relation
      else
        pg start_relation @@ List.init cfa (fun _ -> pl "0")
    in
    let () =
      List.iter (fun (nm,args,_) ->
        pg "declare-fun" [
          pl nm;
          ll @@ ctxt_args @ (
            let pred = fgen nm in
            List.filter_map (fun (p,ty) ->
              if pred p then
                Option.some @@ pp_ztype ty
              else
                None
            ) args
          );
          pl "Bool"
        ] ff.printer;
        break ff
      ) rel;
      List.iter (fun imp ->
        pp_impl ~opts ~fgen imp ff;
        break ff
      ) impl;

      (* now ground the entry point *)
      pg "assert" [
        pg "forall" [
          ll [ ll [ pl "dummy"; pl "Int" ] ];
          grounded
        ]
      ] ff.printer;
      break ff
    in
    SexpPrinter.finish ff;
    ArgOptions.show_cons opts (fun out ->
        let def_file = (ArgOptions.get_intr opts).def_file in
        let output_endline s = output_string out (s ^ "\n") in
        output_endline @@ "; Sending constraints >>>";
        output_endline @@ "; Intrinsic definitions";
        output_endline @@ Option.fold ~none:"" ~some:Files.string_of_file def_file;
        output_endline @@ "; Constraints";
        output_endline @@ SexpPrinter.to_string ff;
        output_endline @@ "; <<<");
    C.solve ~opts ff

  let pprint_annot =
    let open PrettyPrint in
    fun m (i,_) _ ->
      let { gamma; relation; mu_relations } = Std.IntMap.find i m in
      let vars =
        let bindings = List.map (fun (k, t) ->
            pf !"%s: %{FlowInference.fltype_to_string}" k t
          ) gamma |> psep_gen newline
        in
        pblock ~nl:false ~op:(ps "+ Variable Types:") ~body:bindings ~close:null
      in
      let pp_rel (name,args,_) =
        let args = List.map (fun (p,_) -> ps @@ P.to_z3_ident p) args |> psep_gen (pf ",@ ") in
        pl [
          pf "%s(" name;
          pb [ args ];
          ps ")"
        ]
      in
      let mu_rel =
        let body = P.PathMap.bindings mu_relations |> List.map (fun (s,rel) ->
            pb [
              pf !"%{P}:@ " s;
              pp_rel rel;
            ]
            ) |> psep_gen newline
        in
        pblock ~op:(ps "+ Mu Relations:") ~body ~close:null
      in
      let relation =
        pb [
          pf "+ Relation:@ ";
          pp_rel relation
        ]
      in
      let body = psep_gen null [ vars; mu_rel; relation ] in
      pblock ~nl:true ~op:(ps "/*") ~body ~close:(ps "*/")

  let solve ~opts simple_res o_hints ast =
    let rel,impl,snap,start,omit =
      FlowInference.infer ~opts simple_res o_hints ast in
    let fgen =
      if opts.relaxed_mode then
        (fun s ->
           StringMap.find_opt s omit
           |> Option.map (fun s ->
               (fun p -> not @@ P.PathSet.mem p s))
           |> Option.value ~default:(fun _ -> true))
      else (fun _ _ -> true) in
    let ans = solve_constraints ~opts ~fgen rel impl start in
    ArgOptions.show_annotated opts (fun out ->
        AstPrinter.pretty_print_program
          ~with_labels:true ~annot:(pprint_annot snap) out ast);
    ArgOptions.show_ast opts (fun out ->
        let (program_types,_) = simple_res in
        AstPrinter.pretty_print_program out ast;
        StringMap.iter (fun n a ->
            Printf.fprintf out "%s: %s\n" n @@ SimpleTypes.fntype_to_string a)
          program_types);
    ArgOptions.show_ir opts (fun out ->
        let open Std in
        let open Sexplib.Std in
        let mu_bind =
          IntMap.bindings snap
          |> ListMonad.bind (fun (i,pmap) ->
              P.PathMap.bindings pmap.mu_relations
              |> List.map (fun (p,rel) -> (i,p,rel))) in
        let sexp = [%sexp_of: Ast.prog *
                              FlowInference.relation list *
                              (int * P.concr_ap * relation) list
        ] (ast,rel,mu_bind) in
        Sexplib.Sexp.output_hum out sexp);
    ArgOptions.show_model opts (fun out ->
        match ans with
        | Sat Some m -> output_string out (m ^ "\n")
        | _ -> ());
    ans
end

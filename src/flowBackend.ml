
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
     

  let close_and_print rel_op clause =
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
      | NondetChoice (arg::(_::_ as l)) ->
        let%bind fst = pp_arg ty arg in
        mfold_left (fun expr choice ->
          let flg = Printf.sprintf "star!%d" !choice_counter in
          incr choice_counter;
          let id = P.var flg in
          let%bind pp_choice = pp_arg ty choice in
          add_ident id ZBool >>
          return @@ pg "ite" [
              pl flg;
              pp_choice;
              expr
            ]
        ) fst l
      | NondetChoice _ -> assert false
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
      let subst_map = List.fold_left (fun acc (k,v) ->
          Paths.PathMap.add k v acc
        ) Paths.PathMap.empty subst
      in
      let%bind val_args =
        mmap (fun (arg_path,ty) ->
          let subst = Paths.PathMap.find_opt arg_path subst_map in
          match subst with
          | None -> add_ident arg_path ty >> return @@ pp_ap arg_path
          | Some subst -> pp_arg ty subst
        ) formals
      in
      let%bind ctxt_args =
        if !KCFA.cfa = 0 then
          return []
        else
          let tl_adj = Option.fold ~none:0 ~some:(Fun.const 1) ctxt_shift in
          let%bind tail = List.init (!KCFA.cfa - tl_adj) context_at |> List.map P.var |> mmap (fun ap ->
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

  let close_impl relops ante conseq =
    let path_types = Paths.PathMap.empty in
    let path_types,ante_k = mmap (close_and_print relops) ante path_types in
    let ante_k = match ante_k with
      | [] -> pl "true"
      | _ -> pg "and" ante_k
    in
    let path_types,conseq_k = close_and_print relops conseq path_types in
    (path_types,ante_k,conseq_k)

  let pp_impl relops (ante,conseq) ff =
    let (args,ante_k,conseq_k) = close_impl relops ante conseq in
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

  let solve_constraints ~interp:(relops,defn_file) rel impl start_relation =
    let ff = SexpPrinter.fresh () in
    let ctxt_args = List.init !KCFA.cfa (fun _ -> pp_ztype ZInt) in
    let grounded =
      if !KCFA.cfa = 0 then
        pl start_relation
      else
        pg start_relation @@ List.init !KCFA.cfa (fun _ -> pl "0")
    in
    let () =
      List.iter (fun (nm,args,_) ->
        pg "declare-fun" [
          pl nm;
          ll @@ ctxt_args @ List.map (fun (_,ty) -> pp_ztype ty) args;
          pl "Bool"
        ] ff.printer;
        break ff
      ) rel;
      List.iter (fun imp ->
        pp_impl relops imp ff;
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
    C.solve ~defn_file ff

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

  let solve ~annot_infr ~dump_ir ~intr simple_res o_hints ast =
    let open Intrinsics in
    let rel,impl,snap,start = FlowInference.infer ~bif_types:intr.op_interp simple_res o_hints ast in
    let () =
      if annot_infr then
        AstPrinter.pretty_print_program ~with_labels:true ~annot:(pprint_annot snap) stderr ast;
      flush stderr
    in
    let () = Option.iter (fun out_f ->
        let f = open_out out_f in
        Fun.protect ~finally:(fun () -> close_out f) (fun () ->
          let open Std in
          let open FlowInference in
          let open Sexplib.Std in
          let module P = Paths in
          let mu_bind = IntMap.bindings snap |> ListMonad.bind (fun (i,pmap) ->
                P.PathMap.bindings pmap.mu_relations |> List.map (fun (p,rel) -> (i,p,rel))
              )
          in
          Sexplib.Sexp.output_hum f @@ [%sexp_of: Ast.prog * FlowInference.relation list * (int * P.concr_ap * relation) list] (ast,rel,mu_bind);
          flush f;
        )
      ) dump_ir in
    (),solve_constraints ~interp:(intr.rel_interp,intr.def_file) rel impl start
end

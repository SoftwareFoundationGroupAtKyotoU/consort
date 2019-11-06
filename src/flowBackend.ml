
(* TODO: factor this out better *)
module Make(C : Solver.SOLVER_BACKEND) = struct
  type t = unit
  open SexpPrinter
  open FlowInference
  open Std.StateMonad

  module RT = RefinementTypes

  let pp_ap p = pl @@ Paths.to_z3_ident p

  let pp_ztype = function
    | ZInt -> pl "Int"
    | ZBool -> pl "Bool"

  let pp_imm = function
    | RT.RAp p -> pl @@ Paths.to_z3_ident p
    | RT.RConst i -> pl @@ string_of_int i

  let pp_rel_op = function
    | RT.Nu -> assert false
    | RT.RImm r -> pp_imm r

  let add_ident path ty map =
    (Paths.PathMap.update path (function
    | None -> Some ty
    | Some ty' -> if ty' <> ty then failwith "Something has gone wrong" else Some ty'
    ) map),()

  let close_and_print rel_op clause =
    match clause with
    | Relation p ->
      return RefinementTypes.(
          let rel_sym = StringMap.find p.rel_cond rel_op in
          pg rel_sym [
            pp_rel_op p.rel_op1;
            pp_imm p.rel_op2
          ]
        )
    | NamedRel _ -> failwith "Not yet implemented"
    | PRelation (("program-start",[]),[]) -> return @@ pl "true"
    | PRelation ((name,formals),subst) ->
      let subst_map = List.fold_left (fun acc (k,v) ->
          Paths.PathMap.add k v acc
        ) Paths.PathMap.empty subst
      in
      let%bind args =
        mmap (fun (arg_path,ty) ->
          let subst = Paths.PathMap.find_opt arg_path subst_map in
          match subst with
          | None -> add_ident arg_path ty >> return @@ pp_ap arg_path
          | Some (RAp p) -> add_ident p ty >> return @@ pp_ap p
          | Some (RConst i) -> return @@ pl @@ string_of_int i
        ) formals
      in
      return @@ pg name args

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

  let solve_constraints ~interp:(relops,defn_file) (rel,impl) =
    let ff = SexpPrinter.fresh () in
    let () =
      List.iter (fun (nm,args) ->
        pg "declare-fun" [
          pl nm;
          ll @@ List.map (fun (_,ty) -> pp_ztype ty) args;
          pl "Bool"
        ] ff.printer;
        break ff
      ) rel;
      List.iter (fun imp ->
        pp_impl relops imp ff;
        break ff
      ) impl
    in
    SexpPrinter.finish ff;
    C.solve ~defn_file ff

  let solve ~annot_infr:_ ~intr simple_res o_hints ast =
    let open Intrinsics in
    (),solve_constraints ~interp:(intr.rel_interp,intr.def_file) @@ FlowInference.infer simple_res o_hints ast
end

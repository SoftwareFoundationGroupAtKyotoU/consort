open Ast

let typecheck i_gen file =
  let intr = i_gen () in
  let (fn,prog) = AstUtil.parse_file file in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let f_types,SimpleChecker.SideAnalysis.{let_types; _ } = SimpleChecker.typecheck_prog simple_op (fn,prog) in
  let open PrettyPrint in
  AstPrinter.pretty_print_program ~with_labels:true ~annot_fn:(fun f_name ff ->
    pl [
      pf "/* %s */" @@ SimpleTypes.fntype_to_string @@ StringMap.find f_name f_types;
      newline
    ] ff
  ) ~annot:(fun (id,_) e ->
    let open Std in
    match IntMap.find_opt id let_types,e with
    | Some ty,Let (patt,_,_) ->
      let rec patt_loop acc p t =
        match p,t with
        | PVar v,_ -> (pf "%s: %s" v @@ SimpleTypes.type_to_string t)::acc
        | PNone,_ -> acc
        | PTuple pl,`Tuple tl ->
          List.fold_left2 patt_loop acc pl tl
        | _,_ -> assert false
      in
      let ty_list = patt_loop [] patt ty |> List.rev in
      let sz = List.length ty_list in
      if sz = 0 then
        pl [ ps "/* (no bindings) */"; newline ]
      else if sz = 1 then
        pl [ ps "/* "; pl ty_list; ps " */"; newline ]
      else
        pblock
          ~nl:true
          ~op:(ps "/*")
          ~body:(psep_gen newline ty_list)
          ~close:(ps "*/")
    | _ -> null
  ) stdout (fn,prog)

let () =
  let (spec,i_gen) = Intrinsics.option_loader () in
  Files.run_with_file spec "Parse and (simple) typecheck <file>" @@ typecheck i_gen

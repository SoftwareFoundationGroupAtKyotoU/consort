let typecheck ~opts file =
  let ast = AstUtil.parse_file file in
  let intr_op = (ArgOptions.get_intr opts).op_interp in
  let simple_op = RefinementTypes.to_simple_funenv intr_op in
  let simple_res = SimpleChecker.typecheck_prog simple_op ast in
  let f_types, side = simple_res in
  let open Ast in
  let open PrettyPrint in
  let annot_fn f_name =
    let s = SimpleTypes.fntype_to_string @@ StringMap.find f_name f_types in
    pl [pf "/* %s */" s; newline] in
  let from_ty_patt ty patt =
    let rec patt_loop acc p t =
      match p, t with
      | PVar v, _ -> (pf "%s: %s" v @@ SimpleTypes.type_to_string t)::acc
      | PNone, _ -> acc
      | PTuple pl, `Tuple tl -> List.fold_left2 patt_loop acc pl tl
      | _, _ -> assert false in
    let ty_list = patt_loop [] patt ty |> List.rev in
    match List.length ty_list with
    | 0 -> pl [ps "/* (no bindings) */"; newline]
    | 1 -> pl [ps "/* "; pl ty_list; ps " */"; newline]
    | _ -> pblock
             ~nl:true
             ~op:(ps "/*")
             ~body:(psep_gen newline ty_list)
             ~close:(ps "*/")
  in
  let annot (id, _) e =
    match Std.IntMap.find_opt id side.let_types, e with
    | Some ty, Let (patt, _, _) -> from_ty_patt ty patt
    | _ -> null in
  AstPrinter.pretty_print_program ~with_labels:true ~annot_fn ~annot stdout ast

let () =
  let n = ref None in
  let opts = ArgOptions.parse (fun s -> n := Some s) "Parse and (simple) typecheck <file>" in
  match !n with
  | None -> print_endline "No file provided"
  | Some f -> typecheck ~opts f

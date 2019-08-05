open Ast

let rec find_first (i,e) =
  match e with
  | Seq (e1, _) -> find_first e1
  | _ -> i

let get_bindings_for id patt e =
  let rec get_vars acc p =
    let open Ast in
    match p with
    | PVar v -> v::acc
    | PNone -> acc
    | PTuple pl -> List.fold_left get_vars acc pl
  in
  (id,find_first e, get_vars [] patt)

let rec annot_let (id,e) acc =
  match e with
  | NCond (_,e1,e2)
  | Cond (_,e1,e2)
  | Seq (e1,e2) ->
    annot_let e1 acc
    |> annot_let e2
  | Alias (_,_,e)
  | Assign (_,_,e)
  | Assert (_,e)
  | Update (_,_,_,e)
  | EAnnot (_,e) ->
    annot_let e acc
  | EVar _ -> acc
  | Let (patt,_,e) ->
    annot_let e @@ (get_bindings_for id patt e)::acc

let typecheck i_gen file =
  let intr = i_gen () in
  let (fn,prog) = AstUtil.parse_file file in
  let let_bindings =
    List.fold_left
      (fun acc { body; _ } ->
        annot_let body acc
      ) (annot_let prog []) fn
  in
  let print_types = Hashtbl.create 10 in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let f_types,lkp,_ = SimpleChecker.typecheck_prog simple_op (fn,prog) in
  List.iter (fun (tgt_id,src_id,vars) ->
        lkp src_id
        |> Option.map @@ StringMap.filter (fun k _ -> List.mem k vars)
        |> Option.iter @@ Hashtbl.add print_types tgt_id
  ) let_bindings;
  let open PrettyPrint in
  AstPrinter.pretty_print_program ~with_labels:false ~annot_fn:(fun f_name ff ->
    pl [
      pf "/* %s */" @@ SimpleTypes.fntype_to_string @@ StringMap.find f_name f_types;
      newline
    ] ff
  ) ~annot:(fun id f ->
    match Hashtbl.find_opt print_types id with
    | None -> ()
    | Some env ->
      let sz = (StringMap.cardinal env) in
      if sz = 0 then
        pl [ ps "/* empty */"; newline ] f
      else
        let ty_list = StringMap.bindings env
          |> List.map (fun (k,t) ->
            pf "%s: %s" k @@ SimpleTypes.type_to_string t;
          )
          |> psep_gen newline
        in
        if sz = 1 then
          pl [ ps "/* "; ty_list; ps " */"; newline ] f
        else
          pblock
            ~nl:true
            ~op:(ps "/*")
            ~body:ty_list
            ~close:(ps "*/") f
  ) stdout (fn,prog)

let () =
  let (spec,i_gen) = Intrinsics.option_loader () in
  Files.run_with_file spec "Parse and (simple) typecheck <file>" @@ typecheck i_gen

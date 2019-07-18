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
  | Cond (_,e1,e2)
  | Seq (e1,e2) ->
    annot_let e1 acc
    |> annot_let e2
  | Alias (_,_,e)
  | Assign (_,_,e)
  | Assert (_,e)
  | EAnnot (_,e) ->
    annot_let e acc
  | EVar _ -> acc
  | Let (patt,_,e) ->
    annot_let e @@ (get_bindings_for id patt e)::acc

let () =
  let (intr,file) =
    let open Arg in
    let intr_file = ref None in
    let input_file = ref None in
    let spec = [
      ("-intr", String (fun s -> intr_file := Some s), "Use intrinsic file <file>")
    ] in
    let () = parse spec (fun s -> input_file := Some s) "Parse and (simple) typecheck <file>" in
    ((match !intr_file with
    | None -> Intrinsics.empty
    | Some s -> Intrinsics.load s), match !input_file with
      | None -> failwith "No input file specified"
      | Some s -> s)
  in
  let (fn,prog) = AstUtil.parse_file file in
  let acc =
    List.fold_left
      (fun acc { args; body; _ } ->
        let first_id = find_first body in
        annot_let body @@ (first_id, first_id,args)::acc
      ) (annot_let prog []) fn
  in
  let print_types = Hashtbl.create 10 in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let f_types = SimpleChecker.typecheck_prog ~save_types:(fun lkp ->
      List.iter (fun (tgt_id,src_id,vars) ->
        lkp src_id
        |> Option.map @@ StringMap.filter (fun k _ -> List.mem k vars)
        |> Option.iter @@ Hashtbl.add print_types tgt_id
      ) acc
    ) simple_op (fn,prog) in
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
          
      
    

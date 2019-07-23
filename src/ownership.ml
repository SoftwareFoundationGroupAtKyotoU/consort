let print_program ~o_map ~o_printer r ast =
  let open PrettyPrint in
  let print_type (k,t) = 
    let owner_type =
      RefinementTypes.walk_with_bindings_own ~o_map (fun _ _ _ () ->
        ((), ())
      ) (`AVar k) ([],[]) t () |> snd
    in
    RefinementTypes.pp_type_gen (fun k () -> ps k) o_printer owner_type
  in
  let print_type_binding (k,t) =
    let open PrettyPrint in
    pb [
      pf "%s: " k;
      print_type (k,t)
    ]
  in
  let pp_ty_env i =
    let ty_env = Hashtbl.find r.Inference.Result.ty_envs i in
    if (StringMap.cardinal ty_env) = 0 then
      pl [ ps "/* empty */"; newline ]
    else
      let pp_env = StringMap.bindings ty_env
        |> List.map print_type_binding
        |> psep_gen newline
      in
      pblock ~nl:true ~op:(ps "/*") ~body:pp_env ~close:(ps "*/")
  in
  let pp_f_type f =
    let open RefinementTypes in
    let { arg_types; output_types; result_type } = StringMap.find f r.Inference.Result.theta in
    let { Ast.args; _ } = List.find (fun { Ast.name; _ } -> name = f) @@ fst ast in
    let in_types = List.combine args arg_types 
      |> List.map print_type
      |> psep_gen (pf ",@ ")
    in
    let out_types =
      List.combine args output_types
      |> List.map print_type
      |> psep_gen (pf ",@ ")
    in
    pl [
      pb [
        ps "/* ("; in_types; ps ")";
        pf "@ ->@ ";
        ps "("; out_types; pf "@ |@ "; print_type ("<ret>", result_type); ps ") */";
      ];
      newline
    ]
  in
  AstPrinter.pretty_print_program ~annot:pp_ty_env ~annot_fn:pp_f_type stdout ast  

let ownership_infr debug i_gen file =
  let intr = i_gen () in
  let ast = AstUtil.parse_file file in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let (type_hints_g, save_types) = Inference.collect_type_hints ast in
  let f_types = SimpleChecker.typecheck_prog ~save_types simple_op ast in
  let r = Inference.infer ~print_pred:false ~save_types:true ~type_hints:(type_hints_g ()) ~intrinsics:intr.Intrinsics.op_interp f_types ast in
  print_program ~o_map:(fun _ o -> ((),o)) ~o_printer:RefinementTypes.pp_owner r ast;
  let open Inference.Result in
  let open PrettyPrint in
  let o_solve = OwnershipSolver.solve_ownership ?save_cons:!debug r.theta r.ovars r.ownership in
  match o_solve with
  | None -> print_endline "Could not solve ownership constraints"
  | Some soln ->
    print_program ~o_map:(fun _ o ->
        match o with
        | RefinementTypes.OConst o -> (),o
        | RefinementTypes.OVar o -> (),List.assoc o soln
      ) ~o_printer:(pf "%f") r ast

let () =
  let (i_list, gen) = Intrinsics.option_loader () in
  let debug = ref None in
  let spec = ("-save-cons", Arg.String (fun s -> debug := Some s), "Save constraints to <file>") :: i_list in
  Files.run_with_file spec "Run ownership inference on <file>" @@ ownership_infr debug gen
      

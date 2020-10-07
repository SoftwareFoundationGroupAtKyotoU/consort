open Std

let rec filter_ast f (((e_id,_) as pos, raw_exp) as exp)=
    let open Ast in
    match raw_exp with
    | EVar _ ->  exp
    | Cond (x,y,z) -> (pos, Cond(x,filter_ast f y,filter_ast f z))
    | NCond (x,y,z) ->(pos, NCond(x,filter_ast f y,filter_ast f z))
    | Seq(x,y ) -> (pos, Seq(filter_ast f x, filter_ast f y))
    | Assign(x,y, z) ->if f e_id then (pos, Assign(x, y, filter_ast f z)) else  filter_ast f z
    | Update(w, x,y,z) -> if f e_id then(pos,  Update(w, x,y,filter_ast f z)) else  filter_ast f z
    | Let(x,y,z) ->  if f e_id then (pos, Let(x,y,filter_ast f z)) else  filter_ast f z
    | Alias(x,y,z) -> if f e_id then (pos, Alias(x,y,filter_ast f z)) else  filter_ast f z
    | Assert(x,y) -> if f e_id then (pos, Assert(x,filter_ast f y)) else  filter_ast f y
    (*| EAnnot(x,y) -> if f e_id then (pos, EAnnot(x,filter_ast f y)) else  filter_ast f y*)

let filter_program f (fl, exp)=
    let open Ast in
    (List.map (fun fn -> {fn with body = filter_ast f fn.body}) fl, filter_ast f exp)

let constract_slice unsat program = 
    filter_program (fun id -> IntSet.exists (fun x -> x = id) unsat) program

let counterexample_gen debug i_gen o_gen file =
  let intr = i_gen () in
  let ast = AstUtil.parse_file file in
  let simple_op = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let ((_,SimpleChecker.SideAnalysis.{ fold_locs = _; _ }) as simple_res) = SimpleChecker.typecheck_prog simple_op ast in
  let r = OwnershipInference.infer simple_res intr.Intrinsics.op_interp ast in
  let o_solve = OwnershipSolver.solve_ownership ~opts:(o_gen ()) ?save_cons:!debug ?gen_cex:(Some true) (r.OwnershipInference.Result.ovars,r.OwnershipInference.Result.ocons) in
  (*let _ = AstPrinter.pretty_print_program stderr ast in *)
  match o_solve with
  | Unknown -> print_endline "Solver returns unknown; abort"
  | Sat _ -> print_endline "Owership CHECK passed proceed to create an unsafe trace"
  | UnsatCore unsat ->
      print_endline "============ Ownership Failed Dump Slice ============= ";
      print_endline "### Before";
      AstPrinter.pretty_print_program stderr ast;
      print_endline "### After";
      AstPrinter.pretty_print_program stderr (constract_slice unsat ast)

let () =
  let (i_list, gen) = Intrinsics.option_loader () in
  let (o_list, o_gen) = OwnershipSolver.ownership_arg_gen () in
  let debug = ref None in
  let spec = ("-save-cons", Arg.String (fun s -> debug := Some s), "Save constraints to <file>") :: (i_list @ o_list) in
  Files.run_with_file spec "Run counterexample generation on <file>" @@ counterexample_gen debug gen o_gen

open PrettyPrint
open Std
open Std.StateMonad
open Paths
open Ast
open CounterExampleDAG
open Eval
module P = Paths

(*
  Generate execution trace as a counterexample from verfication failure.
*)

(*
  Horn Clause is encoded with following rules:
  enviroment : path -> runtime_value
*)
type relations = FlowInference.relation list


(*
  types for counterexamples
  (i) Ownership slice is a subset of original program causing the same error.
  (ii) UnsafeTrace slice is an execution trace which causes AsertFail or AliasFail actually.
  (ii) Unsafe slice is generated when the given trace is invalid.
 *)

type cex = 
  OwnershipSlice of prog
  | UnsafeTrace of int list
  | UnsafeSlice of prog
  | Unknown

(* let get_previous_node clauses node =  *)
(* 
    There exists A, B, C, D -> node \in clauses.
    This function identifies the previous node. 


*)

(* 
  get callin node from callout node.
  A counterexample graph is in the form like 
  CallOut ->* CallOut ->* .... -> CallIn ->* CallIn.
*)
let get_callin_from_callout (g : graph) node =
  let rec trace g cur nest =

    (*pl [pf "HOGE %d:" nest;pp_node cur;newline] ff;*)
    let get_node = get_node g in
    if (nest = 0 && match cur.ty with CallIn(_) -> true | _ -> false) then cur
    else
      match cur.dst with
      | [x] -> (
          let x = get_node x in
          match x.ty with
          | CallOut _ ->
              trace g x (nest + 1)
          | CallIn _ ->
              trace g x (nest - 1)
          | _ ->
              trace g x nest )

      | [x;y] -> (
          let x = get_node x in
          let y = get_node y in
          (
          match (x.ty, y.ty) with
          | CallOut _, _ ->
             trace g y nest
          | _, CallOut _ ->
             trace g x nest
          | CallIn _, _ -> 
             trace g x (nest-1)
          | _ , _ -> 
             trace g x nest
          )
      )
      | x ::_ -> 
          trace g (get_node x) nest
      | [] ->
          assert false
  in
  trace g node 1

let rec get_trace_for_funcall g callout =
  trace g callout @@ get_callin_from_callout g callout

and trace g (start : node) (goal : node) =
  let get_node = get_node g in
  let rec trace_sub cur =
(*    pl [pp_node cur;newline] ff; *)
    if cur.id = goal.id then [goal]
    else
      match cur.dst with
      | [x]->
          cur :: trace_sub (get_node x)
      | [x; y] ->  begin
          let x = get_node x in
          let y = get_node y in
          match (x.ty, y.ty) with
          | CallOut _, _ ->
              cur :: (get_trace_for_funcall g x @ trace_sub y)
          | _, CallOut _ ->
              cur :: (get_trace_for_funcall g y @ trace_sub x)
          | _, _ -> 
             cur::(trace_sub x)
              end
      
      | x ::_ -> 
          cur :: trace_sub (get_node x)
      | [] ->
          assert false
  in
  trace_sub start

(*
  First we convert a counterexample(= graph) by CHC solver into a trace(= inst list).
  inst should have concrete values for all nondetermistic values.
*)

(* Reorder graph by execution order *)
let (reorder_graph: graph -> graph) = fun graph ->
  let goal = get_goal graph in
  let start = get_false graph in
  let reorderd = List.rev @@ trace graph start goal in
  reorderd


(* let graph2trace: graph -> prog -> relations -> inst list = fun graph prog relations -> 
  let next_node = (List.map Option.some @@ List.tl graph) @ [None] in
  let conv: node -> node option -> inst option = fun node next_node -> None in
[] *)

let generate_cex _prog = ()

let must_cause_failure prog oracle = 
  try
   let _ = eval_main  oracle (Format.formatter_of_out_channel stderr) prog in false 
  with 
  StopEvaluation(RealError(_)) -> true 
  | e -> false

let rec get_nondet_pos_from_lhs patt lhs = 
  let rec loop p l = 
    match p, l with
    | PVar(v), RNone -> [(P.Var v,[], `None)]
    | _ -> []
  in
  match patt,lhs with
  | PVar(s), Mkref(RNone) -> [(P.Var s, [`Deref], `None)]
  | PVar(s), Nondet _-> [(P.Var s, [], `None)]
  | PVar(s), Tuple ts -> 
    let (ans, _) = List.fold_left (fun (vs, acc) y ->
    match y with
    | RNone -> 
     ((P.Var s, [`Proj acc], `None)::vs, acc+1)
    | _ ->  (vs, acc+1)
    ) ([], 0) ts
    in ans
  | PTuple(ps), Tuple(ts) -> List.concat (List.map2 loop ps ts)
  | PTuple _, _ -> []
  | PVar _,_ -> []
  | PNone,  _ -> []
let proj_e_id ((e_id, _), _) = e_id
let rec accmulate_nondet_position (_, e) = 
 (*
    ex)
    let l:e_id_0 = _ in 
    let r:e_id_1  = ...
    get Var(l) from let-e_id_1-* arg

    let a = (_, 1, (mkref _, 3)) in
    let r:e_id_2  = ...
    get Var(a->0) from let-e_id_2-* arg
    get Var(a->2->1->* from let-e_id_2-* arg *)

  let open Ast in
  match e with 
  | Let(patt, lhs, e') -> (proj_e_id e', get_nondet_pos_from_lhs patt lhs ) :: accmulate_nondet_position e'
  | Cond(_, e1, e2) | NCond(_, e1, e2) | Seq(e1, e2) 
  -> accmulate_nondet_position e1 @ accmulate_nondet_position e2
  | Assign(_,_,e')|Update(_,_,_,e')|Alias(_,_,e')|Assert(_,e') -> accmulate_nondet_position e'
  | EVar(_) -> []
let sub name body = 
List.map (fun x -> (name,x)) (accmulate_nondet_position body)
let nondets (fns, main) = 
  sub "main" main  @ (List.concat (List.map (fun x -> sub x.name x.body) fns))

 let oracle_from_node relations nondets node =
  match node.ty with
  | Ast (ast, _, id) -> 
  (
    match List.find_opt (fun (_,(x,_)) -> x=id) nondets with
    | Some((name, (e_id, paths))) -> 
      let p = name ^ "-" ^ string_of_int e_id ^ "-"^show_ast_nodetype ast in
      (
      match List.find_opt (fun (x,_,_) -> x = p) relations with
      | Some((x,y,z)) -> 
          List.map(fun ps -> 
              let bind = List.map2 (fun (x,_) arg -> (x, arg)) y (List.tl node.args) in
              let (v,ret) = List.find (fun (x,_) -> P.compare ps x = 0) bind in 
              ret
          ) paths
      | None -> assert false
      )
    | None -> []
  )
  
  | _ -> []
    


let oracle_from_graph relations nondets graph = 
List.concat(List.map (oracle_from_node relations nondets) graph )




let main ((fns,m) as prog) relations graph =
  (* let exists = IntSet.of_list @@ List.map (fun x -> x.id ) graph in
  let graph = (List.map (fun x -> {x with dst = List.filter (fun y -> IntSet.mem y exists) x.dst})) graph in *)
  let graph = reorder_graph graph in

  let y = nondets prog in
  let oracle = oracle_from_graph relations y graph in
  (* print_string "hoge"; *)
  (* List.iter (fun (_,x) -> List.iter (fun z -> print_string (P.to_z3_ident z)) x) y;*)
  let ff = Format.formatter_of_out_channel stdout in

  (* let _ = List.iter ( fun x -> pl[pp_node x ;newline] ff) graph in *)
  let open AstPrinter in
  let _ = pl [ps "================ Unsafe Trace ===================="; newline; ps "Input = [";
    psep ", " @@ List.map pi oracle ; ps "]" ] ff in
  newline ff;
  (
    try
      let _ = eval_main oracle ff prog in 
      (
      (ps "\n================== Invalid Trace =======================\n") ff;
      UnsafeSlice.unsafe_slicing prog
      )
    with Eval.StopEvaluation(e) ->
        pl [ newline;Eval.pp_err e] ff;
  );
  Format.pp_print_newline ff ()

  
(* -------------------------------------------------------------- *)
let infer_ownership ~opts intr simple_res ast =
  let module OI = OwnershipInference in
  let o_result = OI.infer simple_res intr.Intrinsics.op_interp ast in
  match
    OwnershipSolver.solve_ownership ~opts
      (o_result.OI.Result.ovars, o_result.OI.Result.ocons)
  with
  | Unknown  -> None
  | UnsatCore _ -> None
  (* | UnsatCore _ -> None *)
  | Sat o_soln ->
      let map_ownership = function
        | OwnershipSolver.OVar v ->
            List.assoc v o_soln
        | OwnershipSolver.OConst c ->
            c
      in
      let o_hints =
        { OI.splits=
            OI.SplitMap.map
              (fun (a, b) -> (map_ownership a, map_ownership b))
              o_result.OI.Result.op_record.OI.splits
        ; OI.gen= OI.GenMap.map map_ownership o_result.OI.Result.op_record.gen
        }
      in
      Some (o_hints, o_result)


let get_ast_and_rel ?(opts = OwnershipSolver.default)
    ?(intrinsic_defn = Intrinsics.empty) in_name =
  let ast = AstUtil.parse_file in_name in
  let intr = intrinsic_defn in
  let simple_typing =
    RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp
  in
  let simple_res = SimpleChecker.typecheck_prog simple_typing ast in
  let infer_opt = infer_ownership ~opts intr simple_res ast in
  match infer_opt with
  | None ->
      failwith "ownership slice reported"
  | Some (o_hints, o_result) ->
      let relations, _, _, start_name =
        FlowInference.infer ~bif_types:intrinsic_defn.op_interp simple_res o_hints ast
      in
      (ast, relations, start_name, simple_res, o_hints, o_result)

let parse_file in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  Locations.set_file_name lexbuf in_name 1 ;
  try EldaricaParser.graph EldaricaLexer.read lexbuf with
  | EldaricaParser.Error ->
      let open Lexing in
      failwith
      @@ Printf.sprintf "Parse error at %s"
      @@ Locations.string_of_location lexbuf.lex_start_p
  | Failure _ ->
      let open Lexing in
      failwith
      @@ Printf.sprintf "Lexing error at %s"
      @@ Locations.string_of_location lexbuf.lex_curr_p



let _ =
  let spec, gen = Intrinsics.option_loader () in
  let (o_list, _o_gen) = OwnershipSolver.ownership_arg_gen () in
  let spec = spec @ o_list in
  let intr = gen() in
  let original_program = ref None in
  let cex_trace = ref None in
  let _simple_typing = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let spec =
    ( "-cex-trace"
       , Arg.String (fun s -> cex_trace := Some s)
       , "Eldarica counterexample trace" )
    :: spec
  in
  Arg.parse spec (fun s -> original_program := Some s) "Extract trace" ;
  let original_program, cex_trace =
    match (!original_program, !cex_trace) with
    | None, _ | _, None ->
        failwith "Both orignal and trace file should be provided"
    | Some a, Some b ->
        (a, b)
  in
  let graph = parse_file cex_trace in
  let ast, relations, start_name , _simple_res, _o_hints, _o_result =
    get_ast_and_rel original_program ~intrinsic_defn:(gen ())
  in
  assert (start_name = "program_start");
  main ast relations graph

open CounterExampleDAG 
let parse_file in_name =
  let f = open_in in_name in
  let lexbuf = Lexing.from_channel f in
  Locations.set_file_name lexbuf in_name 1;
  try
    EldaricaParser.graph EldaricaLexer.read lexbuf 
  with
    | EldaricaParser.Error -> let open Lexing in
    failwith @@ Printf.sprintf "Parse error at %s" @@ Locations.string_of_location lexbuf.lex_start_p
    | Failure _ ->
      let open Lexing in
      failwith @@ Printf.sprintf "Lexing error at %s" @@ Locations.string_of_location lexbuf.lex_curr_p

let get_goal_unsafe (g:graph) = 
  List.find  (fun x -> match x.ty with Goal -> true | _ -> false) g
let get_node_unsafe (g:graph) i = 
  List.find  (fun x -> i = x.id) g

let get_false_unsafe (g:graph)= 
  List.find  (fun x -> match x.ty with False -> true | _ -> false) g

let get_callin_from_callout_unsafe (g:graph) name arg = 
  let rec take n l = 
    if n = 0 then [] else
      (match l with
    | [] -> assert false
    | x::y -> x :: (take (n-1) y)
      )
  in
  let actual_args y = take (List.length y) arg in
  List.find  (fun x -> match x.ty with CallIn y when y = name && actual_args x.args = x.args -> true | _ -> false) g

let rec get_trace_for_funcall g callout = 
    match callout.ty with 
    | CallOut(name) -> trace g callout (get_callin_from_callout_unsafe g name callout.args)
    | _ -> assert false

and trace g (start:node) (goal:node) = 
  (* let _ = Printf.printf "Trace from: %s ----> to %s\n" (CounterExampleDAG.show_node start) (CounterExampleDAG.show_node goal) in  *)
  let get_node = get_node_unsafe g in
  let rec trace_sub cur = 
    (* let _ = Printf.printf "Cur : %s\n" (CounterExampleDAG.show_node cur) in *)
    if cur.id = goal.id then [goal] else 
    (
      match cur.dst with
      | [x] -> cur :: (trace_sub (get_node x))
      | [x;y] -> 
          begin 
            let x = get_node x in 
            let y = get_node y in 
            match x.ty, y.ty with
            | CallOut(_) , _-> cur :: get_trace_for_funcall g x @ trace_sub y
            | _, CallOut(_) -> cur :: get_trace_for_funcall g y @ trace_sub x
            | _, _ -> assert false
          end
      | _ -> assert false
    )
    in 
    trace_sub start



let infer_ownership ~opts intr simple_res ast =
  let module OI = OwnershipInference in
  let o_result = OI.infer simple_res intr.Intrinsics.op_interp ast in
  match OwnershipSolver.solve_ownership ~opts (o_result.OI.Result.ovars,o_result.OI.Result.ocons) with
  | None -> None
  | Some o_soln ->
    let map_ownership = function
      | OwnershipSolver.OVar v -> List.assoc v o_soln
      | OwnershipSolver.OConst c -> c
    in
    let o_hints = {
      OI.splits = OI.SplitMap.map (fun (a,b) ->
          (map_ownership a,map_ownership b)
        ) o_result.OI.Result.op_record.OI.splits;
      OI.gen = OI.GenMap.map map_ownership o_result.OI.Result.op_record.gen
    } in
    Some o_hints


let get_ast_and_rel ?(opts=OwnershipSolver.default) ?(intrinsic_defn=Intrinsics.empty)  in_name =
  let ast = AstUtil.parse_file in_name in
  let intr = intrinsic_defn in
  let simple_typing = RefinementTypes.to_simple_funenv intr.Intrinsics.op_interp in
  let simple_res= SimpleChecker.typecheck_prog simple_typing ast in
  let infer_opt = infer_ownership ~opts intr simple_res ast in
  match infer_opt with
  | None -> failwith "no counterexample"
  | Some r ->
    let (relations,_, start_name) = FlowInference.infer ~bif_types:intrinsic_defn.op_interp simple_res r ast in
    (ast, relations, start_name)

let get_var_from_node relations node name = 
  let s = show_nodetype node.ty in
  let (_,rel) = List.find (fun (c, _) -> c = s) relations in
  let module P = Paths in
  let z = List.map2 (fun (c, _) b ->  (P.to_z3_ident c , b)) rel (List.tl node.args) in 
  let (_,s) = List.find  (fun (a,_) -> a = name) z in
  s

(* let rec get_assert_rel_from_ast f ((e_id,_), raw_exp)=
    let g = get_assert_rel_from_ast f in
    let open Ast in
    match raw_exp with
    | EVar _ -> []
    | Cond (_,y,z) 
    | NCond (_,y,z) 
    | Seq(y,z)->(g y) @ (g z)
    | Assign(_,_, z)
    | Let(_, _,z)
    | Update(_, _, _,z) 
    | EAnnot(_, z)
    | Alias(_,_,z) -> g z 
    | Assert(x,y) -> if f e_id then x::(g y) else g y  *)

let get_assert_rel = 
let open Ast in
function
| Assert(x,_) -> [x]
| _ -> [] 

let get_if_cond = 
let open Ast in
function
| Cond(x,_,_) -> [x]
| _ -> [] 

let get_var = 
let open Ast in
function
| EVar(x) -> [x]
| _ -> [] 

let get_letlhs = 
let open Ast in
function
| Let(_,x,_) -> [x]
| _ -> [] 

let get_letvar = 
let open Ast in
function
| Let(PVar(x),_,_) -> [x]
| Let(PNone,_,_) -> ["_"]
| Let(_) -> failwith "Tuple is not supported"
| _ -> [] 

let rec get_something h f ((e_id,_), raw_exp)=
    let g = get_something h f in
    let open Ast in
    let s = if f e_id then h raw_exp else [] in
    s @ (
    match raw_exp with
    | EVar _ -> []
    | Cond (_,y,z) 
    | NCond (_,y,z) 
    | Seq(y,z)->(g y) @ (g z)
    | Assign(_,_, z)
    | Let(_, _,z)
    | Update(_, _, _,z) 
    | EAnnot(_, z)
    | Assert(_,z) -> g z
    | Alias(_,_,z) -> g z 
    )

let get_unsafe h (prog, f) e_id =
  let open Ast in
  let g = (=) e_id in
  let lis = List.concat (h g f :: (List.map (fun x -> h  g x.body) prog) ) in 
  let _ = assert(List.length lis = 1) in
  List.hd lis

let get_rel_unsafe = get_unsafe (get_something get_assert_rel)
let get_if_cond_unsafe = get_unsafe (get_something get_if_cond)
let get_var_unsafe = get_unsafe (get_something get_var)
let get_letvar_unsafe = get_unsafe (get_something get_letvar)
let get_letlhs_unsafe = get_unsafe (get_something get_letlhs)



let imm_op_to f (imm:Ast.imm_op) = 
match imm with
| IVar(s) -> Printf.sprintf "%s: %d " s (f s)
| IInt(s) -> string_of_int s

let map_rel f (rel:Ast.relation) =
  Printf.sprintf "(%s %s %s)" (imm_op_to f rel.rop1) rel.cond (imm_op_to f rel.rop2)

let rec reps n s =
  if n = 0 then "" else s ^ reps (n - 1) s

let deli x = 
match x with
| [] -> "()"
| _ -> 
  let rec sub x = 
    match x with
    | x::[] -> x
    | x::y -> x ^ ", " ^ (sub y)
    | _ -> assert false
  in 
    "(" ^ sub x ^ ")"


let eval_lhs f = 
let open Ast in
(* TODO : Fix when supporting ref*)
function
| Var(s) -> Printf.sprintf "%s: %d " s (f s)
| Const(s) -> string_of_int s
| Call fn_call -> Printf.sprintf "%s%s" fn_call.callee (deli(List.map (fun x -> x ^":"^(string_of_int @@ f x)) fn_call.arg_names))
| _ ->  "?"


let rec last = function
| [x] -> ([],x)
| x::y -> let (z,la) = last y in (x::z, la)
| _ -> assert false

let take_ret = 
(*FIXME *)
last
   


let print_tr level relations (prog:Ast.prog) _graph ({id=_id;ty;args;dst=_dst} as node) nextnode= 
  let ind = reps !level "  " in
  let v = begin
  match ty with
  | Assert(_, e_id) -> 
      let rel = get_rel_unsafe prog e_id in
      Printf.sprintf "assert%s" (map_rel (get_var_from_node relations node ) rel)
  | If(_, e_id) -> 
  (
      let cond = get_if_cond_unsafe prog e_id in
      Printf.sprintf "if(%s: %d)" cond (get_var_from_node relations node cond) 
  )
  | Seq(_,_) -> ""
  | False -> "FALSE"
  | Goal -> "start"
  | CallIn(name) -> 
  (incr level);
  Printf.sprintf "  -- %s%s" name (deli (List.map string_of_int (List.tl args)))
  | CallOut(name) -> begin (decr level); 
  
  let args,ret = take_ret @@ List.tl args  in
  Printf.sprintf "-- %s%s -> %s end"name (deli (List.map string_of_int args)) (string_of_int ret)
  end
  | Var(_,e_id) -> 
      let var= get_var_unsafe prog e_id in
      Printf.sprintf "%s: %d" var (get_var_from_node relations node var) 
  | Let(_, e_id) -> 
      let var = get_letvar_unsafe prog e_id in
      let lhs = get_letlhs_unsafe prog e_id in
      (
      match lhs with
      | Nondet _ -> (Printf.sprintf "_ : %d" (get_var_from_node relations (Option.get nextnode) var))
      | _ -> 
      Printf.sprintf "let %s = %s in" var (eval_lhs (get_var_from_node relations node) lhs)
      )
  | _ -> failwith "Reference is not implemented(print_tr)"
  end in
  ind ^ v
 

let print_trs relations (prog:Ast.prog) graph trace=
let r = ref 0 in
let prod_next = List.map2 (fun a b -> (a,b))  trace (List.map Option.some (List.tl trace) @ [None]) in
List.iter (fun (x,y) -> Printf.printf "%s\n" (print_tr r relations prog graph x y)) prod_next 

let _ = 
  let g = parse_file Sys.argv.(1) in
  let (spec, gen) = Intrinsics.option_loader () in
  Arg.parse spec (fun _ -> ()) "Extract trace";
  let ((fns, main), relations, start_name) = get_ast_and_rel Sys.argv.(2) ~intrinsic_defn:(gen()) in
  let _ = assert(start_name = "program_start") in
  let goal = get_goal_unsafe g in
  let start = get_false_unsafe g in
  let tr = List.rev @@ trace g start goal in
  let _ = List.map (fun x -> Printf.printf "%s\n" (CounterExampleDAG.show_node x) ) tr in
  print_trs relations (fns,main)  g tr 

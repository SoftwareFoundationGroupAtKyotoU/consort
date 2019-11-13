open CounterExampleDAG 
let debug = ref false
let deli_sub x = 
match x with
| [] -> "()"
| _ -> 
  let rec sub x = 
    match x with
    | x::[] -> x
    | x::y -> x ^ ", " ^ (sub y)
    | _ -> assert false
  in 
  sub x
let deli x = 

    "(" ^ deli_sub x ^ ")"


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
  try 
  List.find  (fun x -> match x.ty with Goal -> true | _ -> false) g
  with 
  | _ -> failwith "No goal"
let get_node_unsafe (g:graph) i = 
  List.find  (fun x -> i = x.id) g

let get_false_unsafe (g:graph)= 
  try 
  List.find  (fun x -> match x.ty with False -> true | _ -> false) g
  with
  | _ -> failwith "No False"

let get_callin_from_callout_unsafe (g:graph) node = 
  let rec trace g (cur:node)  nest = 
    let get_node = get_node_unsafe g in
    (* let _ = Printf.eprintf "FindCallIn %s %s\n" (CounterExampleDAG.show_node node) (CounterExampleDAG.show_node cur) in *)
    if nest = 0 && (match cur.ty with CallIn(_) -> true | _ -> false )then cur else 
    (
      match cur.dst with
      | [x] ->(
        let x = get_node x in
        match x.ty with 
        | CallOut(_) -> trace g x (nest+1)
        | CallIn(_) -> trace g x (nest-1)
        | _ -> trace g x nest
      )
      | [x;y] -> 
          begin 
            let x = get_node x in 
            let y = get_node y in 
            match x.ty, y.ty with
            | CallOut(_) , _-> trace g y nest
            | _, CallOut(_) -> trace g x nest
            | _, _ -> assert false
          end
      | _ -> assert false
    )
  in 
    trace g node 1

  (* let actual_args y = take (List.length y) arg in *)
  (* List.find  (fun x -> match x.ty with CallIn y when y = name && actual_args x.args = x.args -> true | _ -> false) g *)

let rec get_trace_for_funcall g callout = 
    match callout.ty with 
    | CallOut(_) -> trace g callout (get_callin_from_callout_unsafe g callout)
    | _ -> assert false

and trace g (start:node) (goal:node) = 
   (* let _ = Printf.eprintf "Trace from: %s ----> to %s\n" (CounterExampleDAG.show_node start) (CounterExampleDAG.show_node goal) in   *)
  let get_node = get_node_unsafe g in
  let rec trace_sub cur = 
    (* let _ = Printf.eprintf "Cur : %s\n" (CounterExampleDAG.show_node_dst cur) in *)
    if cur.id = goal.id then [goal] else 
    (
      match cur.dst with
      | [x] -> cur :: (trace_sub (get_node x))
      | [x;y] -> 
          begin 
            let x = get_node x in 
            let y = get_node y in 
            match x.ty, y.ty with
            | CallOut(_) , _-> cur :: (
              let tmp1 = get_trace_for_funcall g x in
              tmp1 @trace_sub y)
            | _, CallOut(_) -> cur :: 
              (
                let tmp1 = 
                get_trace_for_funcall g y in tmp1 @ trace_sub x
              )
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

let get_value_str relations node name = 
  let s = show_nodetype node.ty in
  let (_,rel) = 
    try 
      List.find (fun (c, _) -> c = s) relations
    with
    | _ -> failwith (s ^ " is not in relations")
  in
    
  let module P = Paths in
  let z = List.map2 (fun (c, _) b ->  (c , b)) rel (List.tl node.args) in 
  let y = List.filter  (fun (a,_) -> 
  P.has_prefix (`AVar(name, false, false)) a ) z in
  let z = List.map (fun (a, v) -> Printf.sprintf "%s: %d" (P.to_z3_ident a) v) y in
  deli_sub z 

let get_var_from_node relations node name = 
  let s = show_nodetype node.ty in
  (* let _ = Printf.eprintf "get_var_from_node %s %s\n" name s in  *)
  let (_,rel) = 
    try 
      List.find (fun (c, _) -> c = s) relations
    with
    | _ -> failwith (s ^ " is not in relations")
  in
  let module P = Paths in
  let z = List.map2 (fun (c, _) b ->  (c , b)) rel (List.tl node.args) in 
  let (_,s) = try 
    List.find  (fun (a,_) -> 
  match a with
  | `AVar(v, false, false) -> v = name
  | _ -> false
  ) z
  with 
    | _ -> failwith (name ^ " is not in args")
  in
  (* let _ = Printf.eprintf "got_var_from_node %s \n" name in  *)
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

let get_assignvar= 
let open Ast in
function
| Assign(x,y,_) -> [(x,y)]
| _ -> [] 

let get_alias= 
let open Ast in
function
| Alias(x,y,_) -> [(x,y)]
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
    | Assert(_,z) 
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
let get_assignvar_unsafe = get_unsafe (get_something get_assignvar)
let get_alias_unsafe = get_unsafe (get_something get_alias)



let imm_op_to f (imm:Ast.imm_op) = 
match imm with
| IVar(s) -> Printf.sprintf "%s: %d " s (f s)
| IInt(s) -> string_of_int s

let imm_op_to2 f (imm:Ast.imm_op) = 
match imm with
| IVar(s) -> Printf.sprintf "%s" (f s)
| IInt(s) -> string_of_int s



let map_rel f (rel:Ast.relation) =
  Printf.sprintf "(%s %s %s)" (imm_op_to f rel.rop1) rel.cond (imm_op_to f rel.rop2)

let rec reps n s =
  if n = 0 then "" else s ^ reps (n - 1) s


let eval_lhs _ g= 
let open Ast in
(* TODO : Fix when supporting ref*)
function
| Var(s) -> g s (*Printf.sprintf "%s: %d " s (f s)*)
| Const(s) -> string_of_int s
| Call fn_call -> Printf.sprintf "%s%s" fn_call.callee (deli(List.map (fun x -> (g x)) fn_call.arg_names))
| Deref x -> "*" ^ g x
| Mkref y -> "mkref " ^ (
  match y with
  | RNone -> assert false
  | RInt s -> string_of_int s
  | RVar s -> g s
)
| _ ->  "?"


let rec last = function
| [x] -> ([],x)
| x::y -> let (z,la) = last y in (x::z, la)
| _ -> assert false

let take_ret = 
(*FIXME *)
last
   


let print_tr level st relations (prog:Ast.prog) _graph ({id=id;ty;args;dst=_dst} as node) nextnode= 
  let ind = reps !level "  " in
  let v = begin
  match ty with
  | Assert(_, e_id) -> 
      let rel = get_rel_unsafe prog e_id in
      Printf.sprintf "assert%s" (map_rel (get_var_from_node relations node ) rel)
  | If(_, e_id) -> 
  (
      (incr level);
      let cond = get_if_cond_unsafe prog e_id in
      let v  = get_var_from_node relations node cond in
      Printf.sprintf "if(%s: %d) goto %s" cond (get_var_from_node relations node cond) 
      (if v = 0 then "else" else "then")
  )
  | Seq(_,_) -> ""
  | False -> "FALSE"
  | Goal -> "start"
  | CallIn(name) -> 
      begin 
  (Stack.push  !level st);
  (incr level);
  (* FIX *)
  Printf.sprintf "  -- %s%s" name (deli (List.map string_of_int (List.tl args)))
      end
  | CallOut(name) -> begin  
   (level := Stack.pop st); 
  let _args,ret = take_ret @@ List.tl args  in
  Printf.sprintf "-- %s(..) -> %s end"name (* (deli (List.map string_of_int args)) *) (string_of_int ret)
  end
  | Var(_,e_id) -> 
      (
      (* (decr level);  *)
      let var= get_var_unsafe prog e_id in
      Printf.sprintf "%s: %d" var (get_var_from_node relations node var) 
      )
  | Let(_, e_id) -> 
      let var = get_letvar_unsafe prog e_id in
      let lhs = get_letlhs_unsafe prog e_id in
      (
      match lhs with
      | Nondet _ -> (Printf.sprintf "let %s = _:%d in" var (get_var_from_node relations (Option.get nextnode) var))
      (* | Deref x -> (Printf.sprintf "let %s = _:%d in" var (get_var_from_node relations (Option.get nextnode) var)) *)
      | _ -> 
      (
        let g = get_value_str relations node in
      Printf.sprintf "let %s = %s in" var (eval_lhs (get_var_from_node relations node) g lhs)
      )
      )
  | Assign(_, e_id) -> 
      let (var, op) = get_assignvar_unsafe prog e_id in
      let g = get_value_str relations node in
      Printf.sprintf "%s := %s;" var (imm_op_to2 g op) 
  | Alias(_, e_id) -> 
      let (var, src) = get_alias_unsafe prog e_id in
      let mem = (
        match src with
        | AVar(s) -> s
        | ADeref(s) -> "*"^s
        | _ -> assert false
      ) in
      Printf.sprintf "alias(%s = %s);" var mem

  | _ -> failwith "Reference is not implemented(print_tr)"
  end in
  (Printf.sprintf "%d:" id) ^ind ^ v
 

let print_trs relations (prog:Ast.prog) graph trace=
let r = ref 1 in
let rr = Stack.create() in
let prod_next = List.map2 (fun a b -> (a,b))  trace (List.map Option.some (List.tl trace) @ [None]) in
List.iter (fun (x,y) -> Printf.printf "%s\n" (print_tr r rr relations prog graph x y)) prod_next 
let _ = 
  let (spec, gen) = Intrinsics.option_loader () in
  let original_program = ref None in 
  let cex_trace = ref None in 
  let spec = ("-show-all", Arg.String (fun _ -> debug := true), "Show debug info to stderr and details") :: spec in
  let spec = ("-cex-trace", Arg.String (fun s -> cex_trace := Some s), "Eldarica counterexample trace") :: spec in

  Arg.parse spec (fun s -> original_program := Some s) "Extract trace"; 
  let original_program, cex_trace = 
  match !original_program, !cex_trace with
  | None,_ | _, None -> failwith "Both orignal and trace file should be provided"
  | Some(a),Some(b) -> (a, b) 
  in
  let g = parse_file cex_trace in
  let ((fns, main), relations, start_name) = get_ast_and_rel original_program ~intrinsic_defn:(gen()) in
  let _ = assert(start_name = "program_start") in
  let goal = get_goal_unsafe g in
  let start = get_false_unsafe g in
  let tr = List.rev @@ trace g start goal in
  print_trs relations (fns,main)  g tr 

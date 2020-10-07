open Std
open Ast
open AstPrinter
open PrettyPrint
let get_imm_set =function IVar s -> StringSet.singleton s | IInt s -> StringSet.empty
let rec eval_src_ap = function
| AVar s -> StringSet.singleton s
| AProj (s, i) -> 
    StringSet.singleton s
| ADeref (s) -> 
    StringSet.singleton s
| APtrProj(s, i) -> 
    StringSet.singleton s
let unite s t st = if StringSet.mem s st then StringSet.add t st else   
                  if StringSet.mem t st then StringSet.add s st else   
                  st
let rec slice st (pos, e) = 
  match e with 
  | EVar(s) -> pos, EVar(s)
  | NCond(s, e1,e2)  -> 
    pos, NCond(s, slice st e1, slice st e2)
  | Cond(s, e1, e2) ->  
    pos, Cond(s, slice st e1, slice st e2)
  | Seq(e1, e2) ->  
    pos, Seq(slice st e1, slice st e2)
  | Assign (t, imm, e1) -> 
              if StringSet.mem t st then  (pos, Assign (t, imm, slice st e1)) else slice st e1
   | Update (t, a, b, e1) -> 
              if StringSet.mem t st then  (pos, Update (t, a,b,slice st e1)) else slice st e1
  | Assert(rel, e1) -> pos, Assert(rel, slice st e1)
  | Alias(left, right, e1) ->pos, Alias(left, right, slice st e1)
  | Let(PVar(t), lhs, e1) -> 
   if StringSet.mem t st then  (pos,Let(PVar(t), lhs,slice st e1)) else slice st e1

let abort = ref false
let rec unsafe_involved_variable st fun_env (_, e) = 
  let rec f_rec = unsafe_involved_variable st fun_env in
  match e with
  | EVar(s) ->  (StringSet.add s st)
  | NCond(s, e1,e2) | Cond(s, e1, e2) ->  
      let st = StringSet.add s st in (StringSet.union (unsafe_involved_variable st fun_env e1)(unsafe_involved_variable st fun_env e2))
  | Seq (e1, e2)  -> 
      (StringSet.union (unsafe_involved_variable st fun_env e1)(unsafe_involved_variable st fun_env e2))
  | Assign (t, imm, e) -> 
      let st = 
      match imm with 
      | IVar s -> if StringSet.mem s st then StringSet.add t st else   
                  if StringSet.mem t st then StringSet.add s st else   
                  st
      | _ ->  st
      in 
        unsafe_involved_variable st fun_env e
   | Update (s, _, t, e) -> 
        let st = 
        if StringSet.mem s st then StringSet.add t st else   
                  if StringSet.mem t st then StringSet.add s st else   
                  st
        in 
        unsafe_involved_variable st fun_env e
  | Assert(({rop1; cond;rop2} as rel), e) -> 
    let r1 = get_imm_set rop1 in
    let r2 = get_imm_set rop2 in
    let st = StringSet.union st(StringSet.union r1 r2) in
    unsafe_involved_variable st fun_env e
  | Alias(left, right, e) -> 
    let r1 = StringSet.singleton left in
    let r2 = eval_src_ap right in
    let st = StringSet.union st(StringSet.union r1 r2) in
    unsafe_involved_variable st fun_env e
  | Let (PNone, lhs, e) -> 
  (
      match lhs with 
        | Call ({callee;arg_names;_} as f) -> 
            let (_,args) = StringMap.find callee fun_env in
            List.fold_left2 (
            fun st s t -> 
                if t then StringSet.add s st else   
                  st
            ) st arg_names args 
        | _ ->
            unsafe_involved_variable st fun_env e
  )
  | Let (PVar s, lhs, e) ->
  (
    match lhs with
       | Call ({callee;arg_names;_} as f) -> 
       (* TODO: FIX*)
        let st = StringSet.union (StringSet.of_list arg_names) st in
         unsafe_involved_variable (StringSet.add s st) fun_env e
       (*
            let (b,args) = StringMap.find_opt callee fun_env in
            let st = if b then StringSet.add s st else st in
            List.fold_left2 (
            fun st s t -> 
                if t then StringSet.add s st else   
                  st
            ) st arg_names args 
        *)
        | Var t 
        | Mkref (RVar t)
        | LengthOf t
        | MkArray t
        | Deref t ->
            unsafe_involved_variable (unite s t st) fun_env e
        | Read (t1, t2) -> 
            unsafe_involved_variable (unite s t2 (unite s t1 st)) fun_env e
        | Tuple(rs) -> 
          let st = List.fold_left (fun st t ->
          match t with 
          | RVar t -> unite s t st
        |  _ -> st) st rs in
            unsafe_involved_variable st fun_env e
        | _ -> 
            unsafe_involved_variable st fun_env e
  )
  | Let(PTuple(tp), lhs, e) ->
    abort := true;
    st

  (* (
    let defined = List.concat(List.map (fun t -> match t with 
          | RNone -> []
          | RInt i -> []
          | RVar i -> [i]) tp) in
    let st = StringSet.union st (StringSet.of_list defined) in
    match lhs with
       | Call ({callee;arg_names;_} as f) -> 
        let st = StringSet.union (StringSet.of_list arg_names) st in
         unsafe_involved_variable (StringSet.add s st) fun_env e
        | Var t 
        | Mkref (RVar t)
        | LengthOf t
        | MkArray t
        | Deref t ->
            List.fold_left (fun st s->  unsafe_involved_variable (unite s t st) fun_env e) (List.concat (List.map (fun x -> tp)))
        | Read (t1, t2) -> 
            unsafe_involved_variable (unite s t2 (unite s t1 st)) fun_env e
        | Tuple(rs) -> 
        let st = List.fold_left (fun st t ->
          match t with 
          | RVar t -> unite s t st
        |  _ -> st) st rs in
            unsafe_involved_variable st fun_env e
        | _ -> 
            unsafe_involved_variable st fun_env e
  ) *)

let slice_func {args;name;body} =
  abort := false;
  let rec slice_sub st = 
    let st2 = unsafe_involved_variable st StringMap.empty body in
    if StringSet.cardinal st = StringSet.cardinal st2 then st else slice_sub st2
  in
  let st = StringSet.of_list args in
  let st = slice_sub st in
  if !abort then(print_string "Currently, not tuple is not supported\n In this case, whole program is taken as a slice\n";  {args;name;body}) else
  {args;name;body=slice st body}

let rec unsafe_slicing (fns, main) = 
  print_string "============ Unsafe Slice =============\n";
  let fns' = List.map slice_func fns in
  let {body=main'} = slice_func {args=[];name="";body=main} in 
  pretty_print_program stdout (fns', main')



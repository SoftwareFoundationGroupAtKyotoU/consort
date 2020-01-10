open PrettyPrint
open Std
open Ast
open Sexplib.Std

type runtime_value = 
  RConst of int | RAddr of int  | RTuple of runtime_value list | RArray of int array | RNull

let rec pp_runtime_value = function
  | RConst i -> pi i
  | RAddr v -> ps (Printf.sprintf "[%d]" v) 
  | RTuple vs -> pl (List.map (fun x -> pl [pp_runtime_value x; ps ","]) vs)
  | RArray ar -> pl [ps "[ "; psep ", " (Array.to_list(Array.map pi ar)); ps "]"]
  | RNull -> ps "null"


type heap = runtime_value IntMap.t

let pp_mem (addr, rt_val) = 
    pl [pi addr; ps " -> "; pp_runtime_value rt_val]

type register = runtime_value StringMap.t

let pp_reg (var, rt_val) = 
    pl [ps var; ps ":"; pp_runtime_value rt_val]


let pp_heap heap =  
    psep ", " @@ List.map pp_mem @@ List.of_seq @@ IntMap.to_seq heap

let pp_register reg =  
    psep ", " @@ List.map pp_reg @@ List.of_seq @@ StringMap.to_seq reg

type env =
{
  fns: fn list;
  register : register;
  heap: heap;
  oracle : int list; (* nodet value *)
  ff: Format.formatter
}

let pp_env env =
    pf "env { reg:{%a}, heap:{%a}} " (ul pp_register) env.register (ul pp_heap) env.heap

type unreal_error = InsufficentNondet | InvalidNondet [@@deriving sexp]
type real_error =  AssertFail of Ast.relation | AliasFail of string * Ast.src_ap | OutOfIndex  [@@deriving sexp]
type error =  UnrealError of unreal_error | RealError of real_error [@@deriving sexp]

exception StopEvaluation of error 





let lkp_reg {register;_ } var= try
 StringMap.find var register
 with _ -> failwith @@ Printf.sprintf "reg %s not found" var
let proj_addr = function RAddr s -> s | _ -> assert false
let proj_int = function  RConst s -> s | _ -> assert false
let proj_array = function RArray s -> s | _ -> assert false
let proj_tuple = function RTuple s -> s | _ -> assert false

let lkp_reg_addr env var = match lkp_reg var env with RAddr s -> s | _ -> assert false
let lkp_reg_int env var = match lkp_reg var env with RConst s -> s | _ -> assert false
let lkp_reg_array env var = match lkp_reg var env with RArray s -> s | _ -> assert false

let lkp_heap {heap;_} addr  = try 
 IntMap.find addr heap  
 with _ -> failwith @@ Printf.sprintf "addr [%d] not found" addr
let update_reg var value ({register; _} as env) = {env with register = StringMap.add var value register}
let update_heap addr value ({heap;_} as env)= {env with heap = IntMap.add addr value heap}  

let consume_nondet env = 
  if List.length env.oracle = 0 then 
    raise (StopEvaluation (UnrealError(InsufficentNondet)))
  else 
  ((List.hd env.oracle, {env with oracle = List.tl env.oracle}))
  
let mkref =  
let r = ref 0 in 
fun () -> incr r ; !r

let mkref_env v env = 
  let new_addr = mkref() in
  (RAddr(new_addr), update_heap new_addr v env)
let eval_ref_contents env =
function 
  RNone -> 
    let (addr, env) = consume_nondet env  in (RAddr(addr), env)
  | RInt i -> (RConst i, env)
  | RVar i -> (lkp_reg env i, env)

let rec refinement_holds env refine v = 
let open RefinementTypes in
match refine with
| Top -> true
| And(r1, r2) -> refinement_holds env r1 v && refinement_holds env r2 v
| ConstEq i -> i = v
| _ -> false (* TODO *)

let hard_code = 
  let cast_ret f = fun x y -> if f x y then 0 else 1 in
  let orf  = fun x y -> let x = x = 0 in let y = y = 0 in if x then 0 else if y then 0 else 1 in
  let anf  = fun x y -> let x = x = 0 in let y = y = 0 in if not x then 1 else if not y then 1 else 0 in

  [("+", (+)); 
   ("-", (-));
   ("*", ( * ));
   ("=", cast_ret (=));
   ("<=", cast_ret(<=));
   ("<", cast_ret(<));
   (">", cast_ret(>));
   (">=", cast_ret(>=));
   ("||", orf );
   ("&&", anf )
   ]

let eval_call fn env =
  match List.assoc_opt fn.callee hard_code , fn.arg_names with
  | Some(f),[x;y]-> Some(f (lkp_reg_int x env) (lkp_reg_int y env))
  | None, _ -> None
  | Some(_), _ -> assert false

let eval_src_ap env = function
| AVar s -> lkp_reg_addr s env
| AProj (s, i) -> 
    let rs = proj_tuple(lkp_reg env s) in
    proj_addr (List.nth rs i)
| _ -> assert false
let merge_env env new_env = {env with oracle = new_env.oracle; heap = new_env.heap}

let rec eval_lhs env dst k = 
let open Ast in
match k with
  | Var s ->
    (lkp_reg env s, env)
  | Const s ->
    (RConst s, env)
  | Deref x ->
    (lkp_heap env (lkp_reg_int x env), env)
  | Mkref (RVar s)-> 
    mkref_env (lkp_reg env s) env
  | Mkref (RInt s)-> 
    mkref_env (RConst s) env
  | Mkref RNone-> 
    let (v,env) = consume_nondet env in 
    mkref_env (RConst v) env
  | Null -> 
    (RNull, env)
  | LengthOf s -> 
    let arr = lkp_reg_array s env in
    (RConst(Array.length arr), env)
  | Read (arr, idx) -> 
    let arr = lkp_reg_array arr env in
    let idx = lkp_reg_int idx env in
    if Array.length arr > idx then
    (RConst(arr.(idx)), env)
    else raise (StopEvaluation(RealError(OutOfIndex)))
  | Tuple(rs) -> 
    let (ts, env) = List.fold_left
      (fun (vs, env) r -> 
        let (v, env) = eval_ref_contents env r in
        (v::vs, env)
      ) ([], env) rs in 
    (RTuple (List.rev ts), env)
  | Nondet (Some(refine)) -> 
    let (v, env) = consume_nondet env in
    if refinement_holds env refine v then (RConst v, env) else 
      raise (StopEvaluation(UnrealError(InvalidNondet)))
  | Nondet (None) -> 
    let (v, env) = consume_nondet env in
    (RConst v, env)
  | MkArray(len) -> 
    let len = lkp_reg_int len env in
    (RArray(Array.make len 0), env)
  | Call ({callee;arg_names;_} as f)-> 
  (
    let open Ast in
    match List.find_opt (fun x -> x.name = callee) env.fns with
    | Some({args;name;body}) -> 
      let args' = List.map (lkp_reg env) arg_names in
      let bind = List.map2 (fun x y -> (x,y)) args args' in
      pl [
        indent_from_here ;
        pf "let %a = %s("
        (ul AstPrinter.pp_patt) dst name;
        (psep ", " (List.map (fun (x,y) -> pl [ps x; ps ": "; pp_runtime_value y]) bind));
        pf ") ";
        newline;
      ] env.ff;
      let reg = StringMap.of_bindings bind in
      let new_env = { env with register = reg} in
      let (ret,new_env) = eval new_env body in
      pl[ ps "return " ; pp_runtime_value ret ; ps ";"; dedent;newline] env.ff;
      (ret,merge_env env new_env)

    | None -> begin 
          match eval_call f env with
          | Some(i) -> (RConst(i), env)
          | _ -> assert false
    end
  )

and eval: env -> Ast.exp -> (runtime_value * env) = fun env ((id,_), exp) -> 
let open Ast in
  let lk_reg = lkp_reg env in
  let lk_reg_int x = match lk_reg x with RConst i -> i | _ -> assert false in
  let lk_reg_addr x = match lk_reg x with RAddr i -> i | _ -> assert false in
  let lk_reg_array x = match lk_reg x with RArray i -> i | _ -> assert false in
  let eval_imm = function IVar s -> lk_reg_int s | IInt s -> s in
  match exp with
  | EVar (s) -> (lk_reg s, env)
  | Cond (s, e1, e2) -> eval env (if lk_reg_int s = 0 then e1 else e2) 
  | NCond (s, e1, e2) -> if lk_reg_int s <> 0 then eval env e1 else  eval env e2
  | Seq (e1, e2) -> let _, new_env = eval env e1 in eval (merge_env env new_env) e2
  | Assign (s, imm, e) -> 
    let addr = lk_reg_addr s in 
    let env = update_heap addr (RConst (eval_imm imm)) env in
    eval env e
  | Update(array, idx, value, e) -> 
    let array = lk_reg_array array in
    let idx = lk_reg_int idx in
    let v = lk_reg_int value in
    if Array.length array > idx then
    (array.(idx) <- v;
    eval env e)
    else raise (StopEvaluation(RealError(OutOfIndex)))

  | Let (PNone, lhs, e) -> 
    let (_, env) = eval_lhs env PNone lhs in
    eval env e
  | Let (PVar s, lhs, e) -> 
    let (v, env) = eval_lhs env (PVar s) lhs in
    eval (update_reg s v env) e
  | Let (PTuple t, lhs, e) -> 
    let (v, env) = eval_lhs env (PTuple t) lhs in
    let rec apply_rec pat tup =
        match pat,tup with 
        | PTuple t, RTuple t' -> 
            List.concat @@ List.map2 apply_rec t t'
        | PVar t, (_ as v) -> [(t, v)]
        | PNone, _ -> []
        | _ , _ -> assert false
    in
    let binds = apply_rec (PTuple t) v in
    let env = List.fold_left (fun env (b,c) -> update_reg b c env) env binds in
    eval env e
  | Assert(({rop1; cond;rop2} as rel), e) -> 
    let rop1' = eval_imm rop1 in
    let rop2' = eval_imm rop2 in
    let f = List.assoc_opt cond hard_code in
    let open AstPrinter in
    pl [
          pf "assert%d(%a %s %a) => assert%d(%d %s %d)" id upp_imm rop1 cond upp_imm rop2 id rop1' cond rop2';
    ] env.ff;
    begin
    match f with
    | Some(f) -> if f rop1' rop2' = 0 then eval env e else 
        raise (StopEvaluation(RealError(AssertFail rel)))
    | None -> assert false
    end
  | Alias(left, right, e) -> 
    let left_addr = lk_reg_addr left in
    let right_addr = eval_src_ap env right in
    if left_addr = right_addr then
        eval env e
    else
        raise (StopEvaluation(RealError(AliasFail(left,right))))


let eval_main oracle ff (fns, main) =
    let init_env = 
        {
            oracle = oracle;
            register = StringMap.empty;
            heap = IntMap.empty;
            fns = fns;
            ff = ff;
        }
    in 
   let ans = eval init_env main in
   ans

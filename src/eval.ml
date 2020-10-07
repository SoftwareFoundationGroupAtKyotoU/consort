open PrettyPrint
open Std
open Ast
open Sexplib.Std
open Format

let indent_from_here ff = pp_open_vbox ff 2

type runtime_addr = RNull | RNonNull of int 
type runtime_value = 
  RConst of int | RAddr of runtime_addr  | RTuple of runtime_value list | RArray of int array 

let ff = Format.formatter_of_out_channel stderr

let rec pp_runtime_value = function
  | RConst i -> pi i
  | RTuple vs -> 
      (
      match vs with
      | [] -> ps "()"
      | x :: y -> 
          pl ( (ps"(")::(pp_runtime_value x)::(List.map (fun x -> pl [ps ",";pp_runtime_value x] ) y) @ [ps ")"])
      )
  | RArray ar -> pl [ps "[ "; psep ", " (Array.to_list(Array.map pi ar)); ps "]"]
  | RAddr(RNull) -> ps "null"
  (*| RAddr(RNonNull v) -> ps (Printf.sprintf "[a%d]" v) *)
  | RAddr(RNonNull v) -> ps (Printf.sprintf "a%d" v) 


let newline ff = pp_force_newline ff ()
type heap = runtime_value IntMap.t

let pp_mem (addr, rt_val) = 
  pl [ps "a"; pi addr; ps " : "; pp_runtime_value rt_val]

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


type unreal_error = InsufficentNondet | InvalidNondet 
type real_error =  AssertFail of Ast.relation | AliasFail of string * Ast.src_ap | OutOfIndex of string* string | NullPointerException of string | ArrayMakeInvalidLength of string * int
type error =  UnrealError of unreal_error | RealError of real_error 
let pp_real_err =
  let open AstPrinter in
 function 
  | AssertFail({ rop1; cond; rop2 }) ->
      pl [
          pf "assert(%a %s %a)" upp_imm rop1 cond upp_imm rop2;
          semi;
        ]
  | AliasFail(x, y) -> 
        pl [
          pf "alias(%s = %a)"  x (ul pp_ap) y;
          semi;
        ]
  | OutOfIndex(x, y) -> 
      pl [
          pf "out-of-index(%s[%s])"  x y;
          semi;
        ]
  | NullPointerException(x) -> 
      pl [
          pf "null-pointer-exception(%s)" x;
          semi;
        ]
  | ArrayMakeInvalidLength(x, y) -> 
      pl [
          pf "array.make.invalid.length(%s: %d)" x y;
          semi;
        ]


let pp_err = function
  | RealError(e) -> pl [ps "AssertRail :"; pp_real_err e ]
  | UnrealError(_) -> ps "Unreal error"

let pp_env env = 
    pf "/* heap:{%a} */" (ul pp_heap) env.heap



exception StopEvaluation of error 



let lkp_reg {register;_ } var= try
 StringMap.find var register
 with _ -> failwith @@ Printf.sprintf "reg %s not found" var
let proj_addr = function RAddr s -> s | _ -> assert false
let proj_int = function  RConst s -> s | _ -> assert false
let proj_array = function RArray s -> s | _ -> assert false
let proj_tuple = function RTuple s -> s | _ -> assert false

let lkp_reg_addr env var = match lkp_reg var env with RAddr s -> s | _ -> assert false
let lkp_reg_int env var = 
  match lkp_reg var env with RConst s -> s | _ -> assert false


let lkp_heap ({heap;_}as env) ptr  =
 match lkp_reg_addr ptr env with
 | RNull -> raise (StopEvaluation(RealError(NullPointerException(ptr))))
 | RNonNull(addr) -> IntMap.find addr heap  
let update_reg var value ({register; _} as env) = {env with register = StringMap.add var value register}
let update_heap' ptr value ({heap;_} as env)= 
match lkp_reg_addr ptr env with
| RNonNull(addr) -> {env with heap = IntMap.add addr value heap}  
| _ -> raise (StopEvaluation(RealError(NullPointerException(ptr))))


let lkp_reg_array env var = match lkp_heap var env with RArray s -> s | _ -> assert false

let update_heap addr value ({heap;_} as env)= 
{env with heap = IntMap.add addr value heap}  

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
  (RAddr(RNonNull(new_addr)), update_heap new_addr v env)
let eval_ref_contents env =
function 
  RNone -> 
    let (addr, env) = consume_nondet env  in (RAddr(RNonNull(addr)), env)
  | RInt i -> (RConst i, env)
  | RVar i -> (lkp_reg env i, env)

let rec refinement_holds env refine v = 
let open RefinementTypes in
match refine with
| Top -> true
| And(r1, r2) -> refinement_holds env r1 v && refinement_holds env r2 v
| ConstEq i -> i = v
| Relation({rel_op1=Nu;rel_cond;rel_op2=RConst(j)})-> 
(
  match rel_cond with
  | "=" -> v = j
  | "<" -> v < j
  | "<=" -> v <= j
  | ">" -> v > j
  | ">=" -> v >= j
  | _ -> false
)

| _ -> false (* TODO *)

let hard_code = 
  let cast_ret f = fun x y -> if f x y then 0 else 1 in
  let orf  = fun x y -> let x = x = 0 in let y = y = 0 in if x then 0 else if y then 0 else 1 in
  let anf  = fun x y -> let x = x = 0 in let y = y = 0 in if not x then 1 else if not y then 1 else 0 in

  [("+", (+)); 
   ("-", (-));
   ("%", (mod));
   ("*", ( * ));
   ("=", cast_ret (=));
   ("<=", cast_ret(<=));
   ("!=", cast_ret(<>));
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

let rec eval_src_ap env = function
| AVar s -> lkp_reg_addr s env
| AProj (s, i) -> 
    let rs = proj_tuple(lkp_reg env s) in
    proj_addr (List.nth rs i)
| ADeref (ptr) -> 
  (* let addr = lkp_reg_addr ptr env in *)
  let v = lkp_heap env ptr in
  proj_addr v
| APtrProj(ptr, i) -> 
  let rs = proj_tuple(lkp_heap env ptr) in
  proj_addr (List.nth rs i)

let merge_env env new_env = {env with oracle = new_env.oracle; heap = new_env.heap; ff = new_env.ff}

let no_name_str s =
String.length s >= 2 && (String.sub s 0 2 = "__")

let no_name x = match x with
| PNone -> true
| PVar s -> no_name_str s
| _ -> false

let rec eval_lhs env dst k = 
let open Ast in
match k with
  | Var s ->
    (lkp_reg env s, env)
  | Const s ->
    (RConst s, env)
  | Deref x ->
    (lkp_heap env x , env)
  | Mkref (RVar s)-> 
    let (v, env) = mkref_env (lkp_reg env s) env in
    begin
    if no_name dst then () else 
    pl [
        pf "let %a = %a in"
        (ul AstPrinter.pp_patt) dst (ul pp_runtime_value) v;
        newline;
      ] env.ff
    end;
    (v, env)
  | Mkref (RInt s)-> 
    let (v, env) = mkref_env (RConst s) env in
    begin
    pl [
        pf "let %a = %a in"
        (ul AstPrinter.pp_patt) dst (ul pp_runtime_value) v;
        ps " ";
        pp_env env;
        newline;
      ] env.ff
    end;
    (v, env)
  | Mkref RNone-> 
    let (v,env) = consume_nondet env in 
    mkref_env (RConst v) env
  | Null -> 
    (RAddr(RNull), env)
  | LengthOf s -> 
    let arr = lkp_reg_array s env in
    (RConst(Array.length arr), env)
  | Read (arr, idx) -> 
    let arr' = arr in
    let idx' = idx in 
    let arr = lkp_reg_array arr env in
    let idx = lkp_reg_int idx env in
    if Array.length arr > idx && idx>=0 then
    (RConst(arr.(idx)), env)
    else raise (StopEvaluation(RealError(OutOfIndex(arr', idx'))))
  | Tuple(rs) -> 
    let (ts, env) = List.fold_left
      (fun (vs, env) r -> 
        let (v, env) = eval_ref_contents env r in
        (v::vs, env)
      ) ([], env) rs in 
    (RTuple (List.rev ts), env)
  | Nondet (Some(refine)) -> 
    let (v, env) = consume_nondet env in
    begin
    pl [
        pf "let %a = /* input */ %d in"
        (ul AstPrinter.pp_patt) dst v;
        newline;
      ] env.ff
    end;
    if refinement_holds env refine v then (RConst v, env) else 
      raise (StopEvaluation(UnrealError(InvalidNondet)))
  | Nondet (None) -> 
    let (v, env) = consume_nondet env in
    begin
    pl [
        pf "let %a = /* input */ %d in"
        (ul AstPrinter.pp_patt) dst v;
        newline;
      ] env.ff
    end;
    (RConst v, env)

  | MkArray(len) -> 
    let len' = lkp_reg_int len env in
    if len' < 0 then 
      raise (StopEvaluation(RealError(ArrayMakeInvalidLength(len, len'))))
    else 
      let (v, env) = mkref_env (RArray(Array.make len' 0)) env in
    begin
    pl [
        pf "let %a = %a in"
        (ul AstPrinter.pp_patt) dst (ul pp_runtime_value) v;
        ps " ";
        pp_env env;
        newline;
      ] env.ff
    end;
    (v, env)

      
  | Call ({callee;arg_names;_} as f)-> 
  (
    let open Ast in
    match List.find_opt (fun x -> x.name = callee) env.fns with | Some({args;name;body}) -> 
      let args' = List.map (lkp_reg env) arg_names in
      let bind = List.map2 (fun x y -> (x,y)) args args' in

      let _ = indent_from_here env.ff in
      begin
        (
      if no_name dst then
        (
      pl [
        pf "%s("
         name;
        (psep ", " (List.map (fun (x,y) -> pl [ps x; ps ": "; pp_runtime_value y]) bind));
        pf ") ";
        newline;
      ] env.ff;)
      else
        (
      pl [
        pf "let %a = %s("
        (ul AstPrinter.pp_patt) dst name;
        (psep ", " (List.map (fun (x,y) -> pl [ps x; ps ": "; pp_runtime_value y]) bind));
        pf ") ";
        newline;
      ] env.ff;)
        )
      end;
      let reg = StringMap.of_bindings bind in
      let new_env = { env with register = reg} in
      let (ret,new_env) = eval new_env body in
      let env = merge_env env new_env in
      pl[ ps "return " ; pp_runtime_value ret ; ps ";  ";  pp_env env; newline] env.ff;
      dedent env.ff;
      (ret, env)

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
  let eval_imm_int = function IVar s -> lk_reg_int s | IInt s -> s in
  let eval_imm = function IVar s -> lk_reg s | IInt s -> RConst(s) in
  match exp with
  | EVar (s) -> (lk_reg s, env)
  | Cond (s, e1, e2) -> 
      (
      pl [
        pf "if (%s%d) -> %s " (if no_name_str s then "" else (s^": ")) (lk_reg_int s) (if lk_reg_int s = 0 then "then" else "else"); newline
      ] env.ff;
      (* indent_from_here env.ff; *)
      let t = eval env (if lk_reg_int s = 0 then e1 else e2) in
      (* dedent env.ff; *) t
      )
  | NCond (s, e1, e2) -> if lk_reg s = RAddr(RNull) then eval env e1 else  eval env e2
  | Seq (e1, e2) -> let _, new_env = eval env e1 in eval (merge_env env new_env) e2
  | Assign (s, imm, e) -> 
    (* let addr = lk_reg_addr s in  *)
    let env = update_heap' s (eval_imm imm) env in
    (
      pl [
        pf "%s := %a;" s (ul pp_runtime_value) (eval_imm imm); ps "  "; pp_env env; newline
      ] env.ff;
    );
    eval env e
  | Update(array_name, idx, value, e) -> 
    let array' = array_name in 
    let idx' = idx in
    let RArray(array) = lkp_heap env array_name in
    let idx = lk_reg_int idx in
    let v = lk_reg_int value in
    if Array.length array > idx && idx >= 0 then
    (array.(idx) <- v;
    pl [
      pf "%s[%d] <- %d;" array_name idx v; ps "  "; pp_env env; newline
      ] env.ff;
    eval env e)
    else raise (StopEvaluation(RealError(OutOfIndex(array', idx'))))

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
    let rop1' = eval_imm_int rop1 in
    let rop2' = eval_imm_int rop2 in
    let f = List.assoc_opt cond hard_code in
    let open AstPrinter in
    pl [
(*          pf "assert(%a:%d %s %a:%d)\n" upp_imm rop1 rop1' cond upp_imm rop2 rop2'; *)
          pf "assert(%d %s %d)\n" rop1' cond rop2';

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

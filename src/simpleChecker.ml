open Ast
open SimpleTypes
open Sexplib.Std
open Std
    
type funtyp_v = {
  arg_types_v: int list;
  ret_type_v: int
}

module TyCons : sig
  type t [@@deriving sexp]
  val equal : t -> t -> bool
  val hash : t -> int
  val fresh : unit -> t
  val to_string : t -> string
  val unwrap : t -> int
end = struct
  type t = int [@@deriving sexp]
  let _ref = ref 0;;

  let equal = (=)
  let hash i = i
  let fresh () =
    let i = !_ref in
    incr _ref;
    i

  let to_string = string_of_int
  let unwrap i = i
end

let rec string_of_typ = function
  | `Var i -> Printf.sprintf "'%d" i
  | `TyCons t -> Printf.sprintf "$%s" @@ TyCons.to_string t
  | `Int -> "int"
  | `Tuple pl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_typ pl
[@@ocaml.warning "-32"]


type 'a c_typ = [
  | `Int
  | `TyCons of TyCons.t
  | `Tuple of 'a list
] [@@deriving sexp]

type typ = [
  typ c_typ
| `Var of int
] [@@deriving sexp]


module TyConsUF = UnionFind.Make(TyCons)
module TyConsResolv = Hashtbl.Make(TyCons)

module SM = StringMap

type funenv = funtyp_v SM.t
let _sexp_of_tyenv = SM.sexp_of_t ~v:sexp_of_typ
type tyenv = typ SM.t

type resolv_map = (int,typ) Hashtbl.t

let _sexp_of_resolv_map r = Hashtbl.fold (fun k v acc ->
    (k,v)::acc
  ) r [] |> [%sexp_of: (int * typ) list]

type tuple_cons = {var: int; ind: int; unif: int}

type sub_ctxt = {
  uf: UnionFind.t;
  cons_uf: TyConsUF.t;
  resolv: resolv_map;
  cons_arg: typ TyConsResolv.t;
}

type fn_ctxt = {
  sub: sub_ctxt;
  fenv: funenv;
  tyenv: tyenv;
  t_cons: (tuple_cons list) ref;
  assign_locs: (int * TyCons.t * typ) list ref
}

let fresh_cons_id sub_ctxt t =
  let id = TyCons.fresh () in
  TyConsResolv.add sub_ctxt.cons_arg id t;
  TyConsUF.register sub_ctxt.cons_uf id;
  id

let fresh_cons sub_ctxt t =
  `TyCons (fresh_cons_id sub_ctxt t)

let abstract_type sub_ctxt t =
  let rec loop = function
    | `TVar _ -> failwith "Not supported"
    | `Mu _ -> failwith "Not supported"
    | `Ref t -> fresh_cons sub_ctxt @@ loop t
    | `Int -> `Int
    | `Tuple tl ->
      `Tuple (List.map loop tl)
  in
  loop t

let make_fenv uf fns =
  List.fold_left (fun acc {name; args; _} ->
    StringMap.add name {
      arg_types_v = List.map (fun _ -> UnionFind.new_node uf) args;
      ret_type_v = UnionFind.new_node uf
    } acc) StringMap.empty fns

let init_tyenv fenv { name; args; _ } =
  let { arg_types_v; _ } = StringMap.find name fenv in
  List.fold_left2 (fun acc name var ->
    StringMap.add name (`Var var) acc) StringMap.empty args arg_types_v

let add_var v t ctxt =
  if StringMap.mem v ctxt.tyenv then
    failwith "variable shadowing"
  else
    { ctxt with tyenv = StringMap.add v t ctxt.tyenv }

let canonicalize sub = function
  | `Var v -> `Var (UnionFind.find sub.uf v)
  | `TyCons v -> `TyCons (TyConsUF.find sub.cons_uf v)
  | t' -> t'

let rec occurs_check sub v (t2: typ) =
  match canonicalize sub t2 with
  | `Var v' when v' = v -> failwith "Malformed recursive type"
  | `Tuple tl -> List.iter (occurs_check sub v) tl
  | `Var _
  | `Int
  | `TyCons _ -> ()

let assign sub var t =
  occurs_check sub var t;
  Hashtbl.add sub.resolv var t  

let rec unify sub_ctxt t1 t2 =
  let unfold t1 =
    match canonicalize sub_ctxt t1 with
    | `Var v -> Hashtbl.find_opt sub_ctxt.resolv v
      |> Option.value ~default:(`Var v)
    | _ -> t1
  in
  match unfold t1,(unfold t2) with
  | `Var v1,`Var v2 ->
    UnionFind.union sub_ctxt.uf v1 v2
  | `Var v1,t
  | t,`Var v1 -> assign sub_ctxt v1 t
  | `Int,`Int -> ()
  | `Tuple tl1,`Tuple tl2 ->
    List.iter2 (unify sub_ctxt) tl1 tl2
  | `TyCons c1,`TyCons c2 ->
    unify_tycons sub_ctxt c1 c2
  | t1',t2' -> failwith @@ Printf.sprintf "Ill-typed; could not unify %s and %s"
        (string_of_typ t1')
        (string_of_typ t2')
and unify_tycons sub_ctxt c1 c2 =
  let c1' = TyConsUF.find sub_ctxt.cons_uf c1 in
  let c2' = TyConsUF.find sub_ctxt.cons_uf c2 in
  if TyCons.equal c1' c2' then
    ()
  else
    let a1 = TyConsResolv.find sub_ctxt.cons_arg c1' in
    let a2 = TyConsResolv.find sub_ctxt.cons_arg c2' in
    TyConsUF.union sub_ctxt.cons_uf c1' c2';
    unify sub_ctxt a1 a2

module IS = Std.IntSet

let rec resolve_with_rec sub v_set k t =
  match canonicalize sub t with
  | `Int -> k IS.empty `Int
  | `TyCons t ->
    let id = TyCons.unwrap t in
    if IS.mem id v_set then
      k (IS.singleton id) @@ `TVar id
    else
      let arg_type = TyConsResolv.find sub.cons_arg t in
      resolve_with_rec sub (IS.add id v_set) (fun is t ->
        if IS.mem id is then
          k (IS.remove id is) @@ `Mu (id,`Ref t)
        else
          k is @@ `Ref t
      ) arg_type
  | `Tuple tl ->
    List.fold_left (fun k_acc t ->
        (fun l is_acc ->
          resolve_with_rec sub v_set (fun is t' ->
            k_acc (t'::l) (IS.union is_acc is)
          ) t
        )
      ) 
      (fun l is ->
          k is @@ `Tuple l
        ) tl [] IS.empty
  | `Var v when not @@ Hashtbl.mem sub.resolv v ->
    k IS.empty `Int
  | `Var v ->
    let t' = Hashtbl.find sub.resolv v in
    resolve_with_rec sub v_set k t'

let process_call lkp ctxt { callee; arg_names; _ } =
  let sorted_args = List.fast_sort Pervasives.compare arg_names in
  let rec find_dup l = match l with
    | [_]
    | [] -> false
    | h::h'::_ when h = h' -> true
    | _::t -> find_dup t
  in
  if find_dup sorted_args then
    failwith "Duplicate variable names detected";
  let { arg_types_v; ret_type_v } =
    try
      StringMap.find callee ctxt.fenv
    with
      Not_found -> failwith @@ "No function definition for " ^ callee
  in
  List.iter2 (fun a_var t_var ->
    unify ctxt.sub (lkp a_var) @@ `Var t_var) arg_names arg_types_v;
  `Var ret_type_v

let dump_sexp p t =
  (p t) |> Sexplib.Sexp.to_string_hum |> print_endline
[@@ocaml.warning "-32"]

let rec process_expr save_type ctxt (id,e) =
  save_type id ctxt.tyenv;
  let resolv = function
    | `Var v -> `Var (UnionFind.find ctxt.sub.uf v)
    | t -> t
  in    
  let lkp n =
    try
      StringMap.find n ctxt.tyenv |> resolv
    with
      Not_found -> failwith @@ Printf.sprintf "Undefined variable %s at expression %d" n id
  in
  let unify_var n typ = unify ctxt.sub (lkp n) typ in
  let unify_imm c = match c with
    | IInt _ -> ();
    | IVar v -> unify_var v `Int
  in
  let unify_ref v t =
    unify ctxt.sub (lkp v) @@ fresh_cons ctxt.sub t
  in
  let fresh_var () =
    let t = UnionFind.new_node ctxt.sub.uf in
    `Var t
  in
  let unify t1 t2 =
    unify ctxt.sub t1 t2
  in
  let fresh_cons t1 =
    fresh_cons ctxt.sub t1
  in
  let save_assign v =
    let assign_t = lkp v in
    let c_id = fresh_cons_id ctxt.sub @@ assign_t in
    ctxt.assign_locs := (id,c_id,assign_t)::!(ctxt.assign_locs);
    c_id
  in
  match e with
  | EVar v -> lkp v
  | Cond (v,e1,e2) ->
    unify_var v `Int;
    let t1 = process_expr save_type ctxt e1 in
    let t2 = process_expr save_type ctxt e2 in
    unify t1 t2; t1
  | NCond (v,e1,e2) ->
    unify_ref v @@ fresh_var ();
    let t1 = process_expr save_type ctxt e1 in
    let t2 = process_expr save_type ctxt e2 in
    unify t1 t2; t1
  | Seq (e1,e2) ->
    process_expr save_type ctxt e1 |> ignore;
    process_expr save_type ctxt e2
  | Assign (v1,IInt _,e) ->
    unify_ref v1 `Int;
    process_expr save_type ctxt e
  | Assign (v1,IVar v2,e) ->
    unify_var v1 @@ `TyCons (save_assign v2);
    process_expr save_type ctxt e
  | Alias (v, ap,e) ->
    let fresh_node () = UnionFind.new_node ctxt.sub.uf in
    let find ap =
      match ap with
      | AVar v -> lkp v
      | ADeref v ->
        let t = lkp v in
        let tv = fresh_node () in
        unify t @@ fresh_cons @@ `Var tv;
        (`Var tv)
      | APtrProj (v,ind) ->
        let tuple_v = fresh_node () in
        let content_v = fresh_node () in
        unify_ref v @@ `Var tuple_v;
        ctxt.t_cons := { var = tuple_v; ind; unif = content_v }::!(ctxt.t_cons);
        `Var content_v
      | AProj (v,ind) ->
        let tuple_v = fresh_node () in
        let content_v = fresh_node () in
        unify_var v @@ `Var tuple_v;
        ctxt.t_cons := { var = tuple_v; ind; unif = content_v }::!(ctxt.t_cons);
        `Var content_v
    in
    unify (lkp v) (find ap);
    process_expr save_type ctxt e
  | Assert ({ rop1; rop2; _ },e) ->
    unify_imm rop1;
    unify_imm rop2;
    process_expr save_type ctxt e
  | EAnnot (g,e) ->
    List.iter (fun (k,t) ->
        unify_var k @@ abstract_type ctxt.sub @@ RefinementTypes.to_simple_type t
      ) g;
    process_expr save_type ctxt e
  | Let (PVar v,Mkref (RVar v'),expr) ->
    let c_id = save_assign v' in
    process_expr save_type (add_var v (`TyCons c_id) ctxt) expr
  | Let (p,lhs,expr) ->
    let v_type =
      match lhs with
      | Var v -> lkp v
      | Const _ -> `Int
      | Mkref i -> begin
          match i with
          | RNone
          | RInt _ -> fresh_cons `Int
          | RVar v ->
            fresh_cons (lkp v)
        end
      | Call c -> process_call lkp ctxt c
      | Nondet -> `Int
      | Deref p ->
        let tv = fresh_var () in
        unify (fresh_cons tv) @@ lkp p;
        tv
      | Null -> fresh_cons @@ fresh_var ()
      | Tuple tl ->
        `Tuple (List.map (function
          | RInt _
          | RNone -> `Int
          | RVar v -> lkp v
          ) tl)
    in
    let rec unify_patt acc p t =
      match p with
      | PVar v -> add_var v t acc
      | PNone -> acc
      | PTuple pl ->
        let (t_list,acc'') = List.fold_right (fun p (t_list,acc') ->
            let t_var = fresh_var () in
            (t_var::t_list,unify_patt acc' p t_var)
          ) pl ([], acc) in
        unify t (`Tuple t_list);
        acc''
    in
    let ctxt' = unify_patt ctxt p v_type in
    process_expr save_type ctxt' expr

let constrain_fn save_type sub fenv ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let t_cons = ref [] in
  let assign_locs = ref [] in
  let ctxt =  { sub; fenv; tyenv; t_cons; assign_locs } in
  let out_type = process_expr save_type ctxt body in
  unify ctxt.sub out_type (`Var (StringMap.find name fenv).ret_type_v);
  !t_cons,!assign_locs

let is_rec_assign sub c t' =
  let canon_c = TyConsUF.find sub.cons_uf c in
  let rec check_loop h_rec t =
    match canonicalize sub t with
    | `Var v ->
      Hashtbl.find_opt sub.resolv v
      |> Option.map @@ check_loop h_rec
      |> Option.value ~default:true
    | `Int -> false
    | `TyCons c ->
      let c_id = TyCons.unwrap c in
      if c = canon_c then true
      else if IS.mem c_id h_rec then
        false
      else
        check_loop (IS.add c_id h_rec) @@ TyConsResolv.find sub.cons_arg c
    | `Tuple tl ->
      List.exists (check_loop h_rec) tl
  in
  check_loop IS.empty t'

let typecheck_prog intr_types (fns,body) =
  let (resolv : (int,typ) Hashtbl.t) = Hashtbl.create 10 in
  let cons_arg = TyConsResolv.create 10 in
  let uf = UnionFind.mk () in
  let cons_uf = TyConsUF.mk () in
  let sub = {
    uf; cons_uf; resolv; cons_arg
  } in
  let fenv_ : funenv = make_fenv uf fns in
  let fenv =
    let lift_const t =
      let t_id = UnionFind.new_node uf in
      Hashtbl.add resolv t_id @@ abstract_type sub t;
      t_id
    in
    StringMap.fold (fun k { arg_types; ret_type } ->
      StringMap.add k {
        arg_types_v = List.map lift_const arg_types;
        ret_type_v = lift_const ret_type;
      }
    ) intr_types fenv_
  in
  let cached : (int,typ SM.t) Hashtbl.t = Hashtbl.create 10 in
  let save_type = Hashtbl.add cached in
  let t_cons',assign_locs' = 
    List.map (constrain_fn save_type sub fenv) fns
    |> List.split
    |> fun (a,b) -> (List.concat a),(List.concat b)
  in
  let t_cons = ref t_cons' in
  let assign_locs = ref assign_locs' in
  process_expr save_type {
    sub; fenv; tyenv = StringMap.empty; t_cons; assign_locs
  } body |> ignore;
  List.iter (fun { var; ind; unif } ->
    let t_typ = Hashtbl.find_opt sub.resolv var in
    match t_typ with
    | None -> failwith "Could not deduce type of tuple"
    | Some (`Tuple tl) ->
      if (List.compare_length_with tl ind) <= 0 then
        failwith @@ Printf.sprintf "Ill-typed: expected tuple of at least length %d, got one of length %d" (ind+1) (List.length tl)
      else
        unify sub (`Var unif) @@ List.nth tl ind
    | Some t' -> failwith @@ "Ill-typed: expected tuple, got " ^ (string_of_typ t')
  ) !t_cons;
  let fold_locs = List.fold_left (fun acc (i,c,t') ->
      if is_rec_assign sub c t' then
        i::acc
      else
        acc
    ) [] !assign_locs
  in
  let get_soln = resolve_with_rec sub IS.empty (fun _ t -> t) in
  let lkp = (fun i ->
    match Hashtbl.find_opt cached i with
    | None -> None
    | Some e ->
      let mapped = SM.map get_soln e in
      Some mapped
  ) in
  (List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
  ) StringMap.empty fns),lkp,fold_locs

open Ast
open SimpleTypes
open Sexplib.Std
    
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
  val weight : t -> int
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
  let weight = unwrap
end

let rec string_of_typ = function
  | `Var i -> Printf.sprintf "'%d" i
  | `TyCons t -> Printf.sprintf "$%s" @@ TyCons.to_string t
  | `Int -> "int"
  | `Tuple pl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_typ pl
  | `Array t' -> Printf.sprintf "[%s]" @@ string_of_typ t'
[@@ocaml.warning "-32"]


type 'a c_typ = [
  | `Int
  | `TyCons of TyCons.t
  | `Tuple of 'a list
  | `Array of 'a
] [@@deriving sexp]

type typ = [
  typ c_typ
| `Var of int
] [@@deriving sexp]


module TyConsUF = UnionFind.Make(TyCons)
module TyConsResolv = Hashtbl.Make(TyCons)

module SM = StringMap
module StringSet = Std.StringSet

type funenv = funtyp_v SM.t
let _sexp_of_tyenv = SM.sexp_of_t ~v:sexp_of_typ
type tyenv = typ SM.t

type resolv_map = (int,typ) Hashtbl.t

let _sexp_of_resolv_map r = Hashtbl.fold (fun k v acc ->
    (k,v)::acc
  ) r [] |> [%sexp_of: (int * typ) list]

type tuple_cons = {var: int; ind: int; unif: int; loc: Lexing.position}

type sub_ctxt = {
  uf: UnionFind.t;
  cons_uf: TyConsUF.t;
  resolv: resolv_map;
  cons_arg: typ TyConsResolv.t;
}

type ptr_op = (int * TyCons.t * typ)

type side_results = {
  t_cons: tuple_cons list;
  assign_locs: ptr_op list;
  deref_locs: ptr_op list;
  let_types: typ Std.IntMap.t;
}

module SideAnalysis = struct
  type results = {
    unfold_locs: Std.IntSet.t;
    fold_locs: Std.IntSet.t;
    let_types:  SimpleTypes.r_typ Std.IntMap.t
  }
end

type simple_results = SimpleTypes.funtyp StringMap.t * SideAnalysis.results

type fn_ctxt = {
  sub: sub_ctxt;
  fenv: funenv;
  tyenv: tyenv;
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
    | `Array t -> `Array (loop (t :> SimpleTypes.r_typ))
  in
  loop t

let make_fenv uf fns =
  List.fold_left (fun acc {name; args; _} ->
    if StringMap.mem name acc then
      failwith @@ "Duplicate function definitions for: " ^ name
    else
      StringMap.add name {
        arg_types_v = List.map (fun _ -> UnionFind.new_node uf) args;
        ret_type_v = UnionFind.new_node uf
      } acc
  ) StringMap.empty fns

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
  | `Array t' -> occurs_check sub v t'
  | `Var _
  | `Int
  | `TyCons _ -> ()

let assign sub var t =
  occurs_check sub var t;
  Hashtbl.add sub.resolv var t  

let rec unify ~loc sub_ctxt t1 t2 =
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
    List.iter2 (unify ~loc sub_ctxt) tl1 tl2
  | `TyCons c1,`TyCons c2 ->
    unify_tycons ~loc sub_ctxt c1 c2
  | `Array t1',`Array t2' ->
    unify ~loc sub_ctxt t1' t2'
  | t1',t2' -> Locations.raise_errorf ~loc
                 "Ill-typed; could not unify %s and %s"
                 (string_of_typ t1')
                 (string_of_typ t2')
and unify_tycons ~loc sub_ctxt c1 c2 =
  let c1' = TyConsUF.find sub_ctxt.cons_uf c1 in
  let c2' = TyConsUF.find sub_ctxt.cons_uf c2 in
  if TyCons.equal c1' c2' then
    ()
  else
    let a1 = TyConsResolv.find sub_ctxt.cons_arg c1' in
    let a2 = TyConsResolv.find sub_ctxt.cons_arg c2' in
    TyConsUF.union sub_ctxt.cons_uf c1' c2';
    unify ~loc sub_ctxt a1 a2

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
  | `Array t' ->
    resolve_with_rec sub v_set (fun is t_lift ->
        match t_lift with
        | `Int -> k is @@ `Array `Int
        | _ -> failwith "Only integer arrays are supported"
      ) t'

let process_call ~loc lkp ctxt { callee; arg_names; _ } =
  let sorted_args = List.fast_sort String.compare arg_names in
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
  let len = List.compare_lengths arg_types_v arg_names in
  if len <> 0 then
     Locations.raise_errorf ~loc "mismatched argument arities for call to %s" callee;
  List.iter2 (fun a_var t_var ->
    unify ~loc ctxt.sub (lkp a_var) @@ `Var t_var) arg_names arg_types_v;
  `Var ret_type_v

let dump_sexp p t =
  (p t) |> Sexplib.Sexp.to_string_hum |> print_endline
      [@@ocaml.warning "-32"]

let rec process_expr ctxt ((id,loc),e) res_acc =
  let resolv = function
    | `Var v -> `Var (UnionFind.find ctxt.sub.uf v)
    | t -> t
  in    
  let lkp n =
    try
      StringMap.find n ctxt.tyenv |> resolv
    with
      Not_found -> failwith @@ Printf.sprintf "Undefined variable %s at %s" n @@ Locations.string_of_location loc
  in
  let unify_var n typ = unify ~loc ctxt.sub (lkp n) typ in
  let unify_ref v t =
    unify ~loc ctxt.sub (lkp v) @@ fresh_cons ctxt.sub t
  in
  let fresh_var () =
    let t = UnionFind.new_node ctxt.sub.uf in
    `Var t
  in
  let unify t1 t2 =
    unify ~loc ctxt.sub t1 t2
  in
  let fresh_cons t1 =
    fresh_cons ctxt.sub t1
  in
  let save_assign v =
    let assign_t = lkp v in
    let c_id = fresh_cons_id ctxt.sub @@ assign_t in
    { res_acc with assign_locs = (id,c_id,assign_t)::res_acc.assign_locs },c_id
  in
  let record_read ty =
    let c_id = fresh_cons_id ctxt.sub ty in
    { res_acc with deref_locs = (id,c_id,ty)::res_acc.deref_locs },c_id
  in
  let record_tcons tup_var ind pvar acc =
    { acc with t_cons = { var = tup_var; ind; unif = pvar; loc }::acc.t_cons }
  in
  let save_let ty acc =
    { acc with let_types = Std.IntMap.add id ty acc.let_types }
  in
  let (>||>) (a,t1) b =
    let (a',t2) = b a in
    unify t1 t2;
    a',t2
  in
  let (>>) (a,_) b =
    b a
  in
  let unify_imm imm t =
    match imm with
    | IInt _ -> unify `Int t
    | IVar v -> unify_var v t
  in
  match e with
  | EVar v -> res_acc,lkp v
  | Cond (v,e1,e2) ->
    unify_var v `Int;
    process_expr ctxt e1 res_acc
    >||> process_expr ctxt e2
  | NCond (v,e1,e2) ->
    unify_ref v @@ fresh_var ();
    process_expr ctxt e1 res_acc
    >||> process_expr ctxt e2
  | Seq (e1,e2) ->
    process_expr ctxt e1 res_acc
    >> process_expr ctxt e2
  | Assign (v1,IInt _,e) ->
    unify_ref v1 `Int;
    process_expr  ctxt e res_acc
  | Assign (v1,IVar v2,e) ->
    let acc,c_id = save_assign v2 in
    unify_var v1 @@ `TyCons c_id;
    process_expr ctxt e acc
  | Update (v1,ind,u,e) ->
    let d = fresh_var () in
    unify_var v1 @@ `Array d;
    unify_var ind `Int;
    unify_var u @@ d;
    process_expr ctxt e res_acc
  | Alias (v, ap,e) ->
    let fresh_node () = UnionFind.new_node ctxt.sub.uf in
    let find ap =
      match ap with
      | AVar v -> res_acc,lkp v
      | ADeref v ->
        let tv = fresh_var () in
        let acc,c_id = record_read @@ tv in
        unify_var v @@ `TyCons c_id;
        acc,tv
      | AProj (v,ind) ->
        let tuple_v = fresh_node () in
        let content_v = fresh_node () in
        unify_var v @@ `Var tuple_v;
        (record_tcons tuple_v ind content_v res_acc),`Var content_v
      | APtrProj (v,ind) ->
        let tuple_v = fresh_node () in
        let content_v = fresh_node () in
        let acc,c_id = record_read @@ `Var tuple_v in
        unify_var v @@ `TyCons c_id;
        (record_tcons tuple_v ind content_v acc),`Var content_v
    in
    let (acc,ty) = find ap in
    unify (lkp v) ty;
    process_expr ctxt e acc
  | Assert ({ rop1; rop2; _ },e) ->
    unify_imm rop1 `Int;
    unify_imm rop2 `Int;
    process_expr ctxt e res_acc
  | Let (PVar v,Mkref (RVar v'),expr) ->
    let acc,c_id = save_assign v' in
    process_expr (add_var v (`TyCons c_id) ctxt) expr @@ save_let (`TyCons c_id) acc
  | Let (p,lhs,expr) ->
    let res_acc',v_type =
      let same t = res_acc,t in
      match lhs with
      | Var v -> same @@ lkp v
      | Const _ -> same `Int
      | Mkref i -> same @@ begin
          match i with
          | RNone
          | RInt _ -> fresh_cons `Int
          | RVar v ->
            fresh_cons (lkp v)
        end
      | Call c -> same @@ process_call ~loc lkp ctxt c
      | Nondet _ -> same `Int
      | LengthOf v ->
        let tv = fresh_var () in
        unify_var v @@ `Array tv;
        same @@ `Int
      | Deref p ->
        let tv = fresh_var () in
        let acc',c_id = record_read tv in
        unify_var p @@ `TyCons c_id;
        acc',tv
      | Null -> same @@ fresh_cons @@ fresh_var ()
      | Tuple tl ->
        let _ = List.fold_left (fun acc r ->
            match r with
            | RInt _
            | RNone -> acc
            | RVar v ->
              if StringSet.mem v acc then
                failwith "Duplicate variables in tuple constructor"
              else
                StringSet.add v acc
          ) StringSet.empty tl
        in
        same @@ `Tuple (List.map (function
          | RInt _
          | RNone -> `Int
          | RVar v -> lkp v
            ) tl)
      | MkArray v ->
        unify_var v `Int;
        same @@ `Array (fresh_var ())
      | Read (b,i) ->
        unify_var i `Int;
        let cont = fresh_var () in
        unify_var b @@ `Array cont;
        same cont
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
    process_expr ctxt' expr @@ save_let v_type res_acc'

let constrain_fn sub fenv acc ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let ctxt =  { sub; fenv; tyenv  } in
  let acc',out_type = process_expr ctxt body acc in
  unify ~loc:Lexing.dummy_pos ctxt.sub out_type (`Var (StringMap.find name fenv).ret_type_v);
  acc'

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
    | `Array t' -> check_loop h_rec t'
  in
  check_loop IS.empty t'

let get_rec_loc sub p_ops =
  List.fold_left (fun acc (i,c,t') ->
      if is_rec_assign sub c t' then
        i::acc
      else
        acc
    ) [] p_ops

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
  let acc = List.fold_left (constrain_fn sub fenv)  {
      t_cons = [];
      assign_locs = [];
      deref_locs = [];
      let_types = Std.IntMap.empty
    } fns
  in
  let (acc',_) = process_expr {
    sub; fenv; tyenv = StringMap.empty; 
    } body acc
  in
  List.iter (fun { var; ind; unif; loc } ->
    let v' = UnionFind.find sub.uf var in
    let t_typ = Hashtbl.find_opt sub.resolv v' in
    match t_typ with
    | None -> Locations.raise_errorf ~loc  "Could not deduce type of tuple"
    | Some (`Tuple tl) ->
      if (List.compare_length_with tl ind) <= 0 then
        failwith @@ Printf.sprintf "Ill-typed: expected tuple of at least length %d, got one of length %d" (ind+1) (List.length tl)
      else
        unify ~loc sub (`Var unif) @@ List.nth tl ind
    | Some t' -> failwith @@ "Ill-typed: expected tuple, got " ^ (string_of_typ t')
  ) acc'.t_cons;
  let fold_locs = get_rec_loc sub acc'.assign_locs in
  let unfold_locs = get_rec_loc sub acc'.deref_locs in  
  let get_soln = resolve_with_rec sub IS.empty (fun _ t -> t) in
  (List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
   ) StringMap.empty fns),SideAnalysis.(
    { unfold_locs = Std.IntSet.of_list unfold_locs;
      fold_locs = Std.IntSet.of_list fold_locs;
      let_types = Std.IntMap.map get_soln acc'.let_types
    })

open Ast
open SimpleTypes
open Sexplib.Std
open Std
    
type 'a c_typ = [
  | `Int
  | `Ref of 'a
  | `Tuple of 'a list
] [@@deriving sexp]

type typ = [
  typ c_typ
| `Var of int
] [@@deriving sexp]

let rec string_of_typ = function
  | `Var i -> Printf.sprintf "'%d" i
  | `Ref t -> Printf.sprintf "%s ref" @@ string_of_typ t
  | `Int -> "int"
  | `Tuple pl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_typ pl
[@@ocaml.warning "-32"]

type c_inst = typ c_typ

type funtyp_v = {
  arg_types_v: int list;
  ret_type_v: int
}

module SM = StringMap

type funenv = funtyp_v SM.t
let _sexp_of_tyenv = SM.sexp_of_t ~v:sexp_of_typ
type tyenv = typ SM.t

type resolv_map = (int,typ) Hashtbl.t

let _sexp_of_resolv_map r = Hashtbl.fold (fun k v acc ->
    (k,v)::acc
  ) r [] |> [%sexp_of: (int * typ) list]

type tuple_cons = {var: int; ind: int; unif: int}

type fn_ctxt = {
  uf: UnionFind.t;
  resolv: resolv_map;
  fenv: funenv;
  tyenv: tyenv;
  t_cons: (tuple_cons list) ref
}

let abstract_type uf resolv t =
  let module IM = Std.IntMap in
  let rec loop map = function
    | `TVar id -> `Var (IM.find id map)
  | `Ref t -> `Ref (loop map t)
  | `Int -> `Int
  | `Tuple tl ->
    `Tuple (List.map (loop map) tl)
  | `Mu (v,t) ->
    let i = UnionFind.new_node uf in
    let t' = loop (IM.add v i map) t in
    Hashtbl.add resolv i t'; t'
  in
  loop IM.empty t

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

let rec canonical_type uf r =
  match r with
  | `Var v ->
    let id = UnionFind.find uf v in
    `Var id
  | `Ref t -> `Ref (canonical_type uf t)
  | `Tuple tl ->
    `Tuple (List.map (canonical_type uf) tl)
  | _ -> r

let canonicalize ctxt (r: typ) =
  canonical_type ctxt.uf r

let unfold uf resolv = function
  | `Var v ->
    let v' = UnionFind.find uf v in
    Hashtbl.find_opt resolv v'
    |> Option.map @@ canonical_type uf
    |> Option.value ~default:(`Var v)
  | t -> t

let rec unify_inner ?(hyp_set=CoHypS.empty) uf resolv t1 t2 =
  if t1 = t2 then ()
  else
    let next_set =
      match t1,t2 with
      | `Var v1,`Var v2 when CoHypS.mem (v1,v2) hyp_set ->
        CoHypS.iter (fun (a,b) ->
            UnionFind.union uf a b
          ) hyp_set;
        None
      | `Var v1,`Var v2 ->
        Some (CoHypS.add (v1,v2) hyp_set)
      | _,_ -> Some hyp_set
    in
    Option.iter (fun h_set ->
      let ty_assign v ty = Hashtbl.add resolv v ty in
      match (unfold uf resolv t1, unfold uf resolv t2) with
      | (`Var v1, `Var v2) -> UnionFind.union uf v1 v2
      | (`Var v1, (#c_inst as ct))
      | (#c_inst as ct, `Var v1) ->
        ty_assign v1 ct
      | (`Ref t1',`Ref t2') ->
        unify_inner ~hyp_set:h_set uf resolv t1' t2'
      | (`Tuple tl1, `Tuple tl2) ->
        List.iter2 (unify_inner ~hyp_set:h_set uf resolv) tl1 tl2
      | (u1,u2) when u1 = u2 -> ()
      | (u1,u2) -> failwith @@ Printf.sprintf "Ill-typed (cannot unify %s and %s)" (string_of_typ u1) (string_of_typ u2)
    ) next_set

let unify ctxt t1 t2 =
  unify_inner ctxt.uf ctxt.resolv t1 t2

module IS = Set.Make(struct
    type t = int
    let compare = (-)
  end)

let rec resolve_with_rec res f v_set k t =
  match f t with
  | `Int -> k IS.empty `Int
  | `Ref t' -> resolve_with_rec res f v_set (fun is t ->
                   k is @@ `Ref t) t'
  | `Tuple tl ->
    List.fold_left (fun k_acc t ->
        (fun l is_acc ->
          resolve_with_rec res f v_set (fun is t' ->
            k_acc (t'::l) (IS.union is_acc is)
          ) t
        )
      ) 
      (fun l is ->
          k is @@ `Tuple l
        ) tl [] IS.empty
  | `Var v when IS.mem v v_set -> k (IS.singleton v) @@ `TVar v
  | `Var v when not @@ Hashtbl.mem res v ->
    k IS.empty `Int
  | `Var v ->
    resolve_with_rec res f (IS.add v v_set) (fun is t ->
        if IS.mem v is then
          k (IS.remove v is) @@ `Mu (v,t)
        else
          k is t
      ) @@ Hashtbl.find res v

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
    unify ctxt (lkp a_var) @@ `Var t_var) arg_names arg_types_v;
  `Var ret_type_v

let dump_sexp p t =
  (p t) |> Sexplib.Sexp.to_string_hum |> print_endline
[@@ocaml.warning "-32"]

let rec process_expr save_type ctxt (id,e) =
  save_type id ctxt.tyenv;
  let res t = canonicalize ctxt t in
  let lkp n =
    try
      StringMap.find n ctxt.tyenv |> res
    with
      Not_found -> failwith @@ Printf.sprintf "Undefined variable %s at expression %d" n id
  in
  let unify_var n typ = unify ctxt (lkp n) typ in
  let unify_imm c = match c with
    | IInt _ -> ();
    | IVar v -> unify_var v `Int
  in
  let unify_ref v t =
    unify ctxt (lkp v) @@ `Ref t
  in
  let fresh_var () =
    let t = UnionFind.new_node ctxt.uf in
    `Var t
  in
  match e with
  | EVar v -> lkp v
  | Cond (v,e1,e2) ->
    unify_var v `Int;
    let t1 = process_expr save_type ctxt e1 in
    let t2 = process_expr save_type ctxt e2 in
    unify ctxt t1 t2; t1
  | NCond (v,e1,e2) ->
    unify_ref v @@ fresh_var ();
    let t1 = process_expr save_type ctxt e1 in
    let t2 = process_expr save_type ctxt e2 in
    unify ctxt t1 t2; t1
  | Seq (e1,e2) ->
    process_expr save_type ctxt e1 |> ignore;
    process_expr save_type ctxt e2
  | Assign (v1,IInt _,e) ->
    unify_ref v1 `Int;
    process_expr save_type ctxt e
  | Assign (v1,IVar v2,e) ->
    unify_ref v1 @@ lkp v2;
    process_expr save_type ctxt e
  | Alias (v, ap,e) ->
    let find ap =
      match ap with
      | AVar v -> lkp v
      | ADeref v ->
        let t = lkp v in
        let tv = UnionFind.new_node ctxt.uf in
        unify ctxt t (`Ref (`Var tv));
        (`Var tv)
      | APtrProj (v,ind) ->
        let tuple_v = UnionFind.new_node ctxt.uf in
        let content_v = UnionFind.new_node ctxt.uf in
        unify_ref v @@ `Var tuple_v;
        ctxt.t_cons := { var = tuple_v; ind; unif = content_v }::!(ctxt.t_cons);
        `Var content_v
      | AProj (v,ind) ->
        let tuple_v = UnionFind.new_node ctxt.uf in
        let content_v = UnionFind.new_node ctxt.uf in
        unify_var v @@ `Var tuple_v;
        ctxt.t_cons := { var = tuple_v; ind; unif = content_v }::!(ctxt.t_cons);
        `Var content_v
    in
    unify ctxt (lkp v) (find ap);
    process_expr save_type ctxt e
  | Assert ({ rop1; rop2; _ },e) ->
    unify_imm rop1;
    unify_imm rop2;
    process_expr save_type ctxt e
  | EAnnot (g,e) ->
    List.iter (fun (k,t) ->
        unify_var k @@ abstract_type ctxt.uf ctxt.resolv @@ RefinementTypes.to_simple_type t
      ) g;
    process_expr save_type ctxt e
  | Let (p,lhs,expr) ->
    let v_type =
      match lhs with
      | Var v -> lkp v
      | Const _ -> `Int
      | Mkref i -> begin
          match i with
          | RNone
          | RInt _ -> `Ref `Int
          | RVar v -> `Ref (lkp v)
        end
      | Call c -> process_call lkp ctxt c
      | Nondet -> `Int
      | Deref p ->
        let tv = fresh_var () in
        unify ctxt (`Ref tv) @@ lkp p;
        canonicalize ctxt tv
      | Null -> `Ref (fresh_var ())
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
        unify ctxt t (`Tuple t_list);
        acc''
    in
    let ctxt' = unify_patt ctxt p v_type in
    process_expr save_type ctxt' expr

let constrain_fn save_type uf fenv resolv ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let t_cons = ref [] in
  let ctxt =  { uf; fenv; tyenv; resolv; t_cons } in
  let out_type = process_expr save_type ctxt body in
  unify ctxt out_type (`Var (StringMap.find name fenv).ret_type_v);
  !t_cons

let typecheck_prog ?save_types intr_types (fns,body) =
  let (resolv : (int,typ) Hashtbl.t) = Hashtbl.create 10 in
  let uf = UnionFind.mk (fun ~parent ~child ->
      if Hashtbl.mem resolv child then
        Hashtbl.add resolv parent (Hashtbl.find resolv child)
      else ()
    ) in
  let fenv_ : funenv = make_fenv uf fns in
  let fenv =
    let lift_const t =
      let t_id = UnionFind.new_node uf in
      Hashtbl.add resolv t_id @@ abstract_type uf resolv t;
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
  let save_type : int -> typ SM.t -> unit = match save_types with
    | None -> (fun _ _ -> ())
    | Some _ -> Hashtbl.add cached
  in
  let t_cons = ref @@ (List.map (constrain_fn save_type uf fenv resolv) fns |> List.concat) in
  process_expr save_type {
    resolv; uf; fenv; tyenv = StringMap.empty; t_cons
  } body |> ignore;
  List.iter (fun { var; ind; unif } ->
    let t_typ = Hashtbl.find_opt resolv var in
    match t_typ with
    | None -> failwith "Could not deduce type of tuple"
    | Some (`Tuple tl) ->
      if (List.compare_length_with tl ind) <= 0 then
        failwith @@ Printf.sprintf "Ill-typed: expected tuple of at least length %d, got one of length %d" (ind+1) (List.length tl)
      else
        unify_inner uf resolv (`Var unif) @@ List.nth tl ind
    | Some t' -> failwith @@ "Ill-typed: expected tuple, got " ^ (string_of_typ t')
  ) !t_cons;
  let get_soln = resolve_with_rec resolv (canonical_type uf) IS.empty (fun _ t -> t) in
  (match save_types with
  | None -> ()
  | Some f -> f (fun i ->
                  match Hashtbl.find_opt cached i with
                  | None -> None
                  | Some e ->
                    let mapped = SM.map get_soln e in
                    Some mapped
                ));
  List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
  ) StringMap.empty fns

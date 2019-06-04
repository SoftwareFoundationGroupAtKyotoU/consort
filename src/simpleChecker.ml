open Ast
open SimpleTypes

module UnionFind : sig
  type t
  val find: t -> int -> int
  val union: t -> int -> int -> unit
  val mk: (parent:int -> child:int -> unit) -> t
  val new_node: t -> int
end = struct
  type node = {
    id: int;
    mutable parent: node;
    mutable rank: int;
  }
  
  type t = {
    table: (int, node) Hashtbl.t;
    mutable next: int;
    merge_hook : parent:int -> child:int -> unit
  }

  let make_and_add uf =
    let rec node = { id = uf.next; parent = node; rank = 1 } in
    Hashtbl.add uf.table node.id node;
    uf.next <- uf.next + 1;
    node.id

  let mk merge_hook =
    let uf = { table = Hashtbl.create 10; next = 0; merge_hook } in
    (*List.iter (fun r ->
      Some r |> (make_and_add uf) |> ignore
    ) roots;*)
    uf

  let rec compress node =
    if node.parent == node then
      node
    else
      let found = compress node.parent in
      node.parent <- found;
      found

  let find_internal uf id1 =
    let node = Hashtbl.find uf.table id1 in
    (compress node)

  let find uf id1 =
    (find_internal uf id1).id

  let union uf id1 id2 =
    let n1 = find_internal uf id1 in
    let n2 = find_internal uf id2 in
    if n1 == n2 then
      ()
    else begin
      let (new_root,child) = begin
        if n2.rank < n1.rank then
          (n2.parent <- n1; (n1,n2))
        else if n1.rank < n2.rank then
          (n1.parent <- n2; (n2,n1))
        else
          (let (new_root,child) = (n1,n2) in
          child.parent <- new_root;
          new_root.rank <- new_root.rank + 1;
          (new_root,child))
      end in
      uf.merge_hook ~parent:new_root.id ~child:child.id
    end

  let new_node uf = make_and_add uf
end

module StringMap = Map.Make(String)

type typ = [
  | `Var of int
  | r_typ
]

type funtyp_v = {
  arg_types_v: int list;
  ret_type_v: int
}

type funenv = funtyp_v StringMap.t
type tyenv = typ StringMap.t

type fn_ctxt = {
  uf: UnionFind.t;
  resolv: (int,r_typ) Hashtbl.t;
  fenv: funenv;
  tyenv: tyenv
}

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

let resolve_type uf resolv r =
  match r with
  | #r_typ -> r
  | `Var v ->
    let id = UnionFind.find uf v in
    if Hashtbl.mem resolv id then
      (Hashtbl.find resolv id :> typ)
    else r

let force_resolve uf resolv t : r_typ =
  match resolve_type uf resolv t with
  | #r_typ as out -> out
  | _ -> failwith "Unconstrained value"

let resolve ctxt (r: typ) =
  resolve_type ctxt.uf ctxt.resolv r

let unify ctxt t1 t2 =
  let ty_assign v ty = Hashtbl.add ctxt.resolv v ty in
  match (resolve ctxt t1, resolve ctxt t2) with
  | (`Var v1, `Var v2) -> UnionFind.union ctxt.uf v1 v2
  | (`Var v1, (#r_typ as t)) | (#r_typ as t, `Var v1) -> ty_assign v1 t
  | ((#r_typ as t1), (#r_typ as t2)) when t1 = t2 -> ()
  | _ -> failwith "Ill-typed"

let process_call lkp ctxt { callee; arg_names; _ } =
    let { arg_types_v; ret_type_v } = StringMap.find callee ctxt.fenv in
    List.iter2 (fun a_var t_var ->
      unify ctxt (lkp a_var) @@ `Var t_var) arg_names arg_types_v;
    `Var ret_type_v

let rec process_expr ctxt e =
  let res t = resolve ctxt t in
  let lkp n = StringMap.find n ctxt.tyenv |> res in
  let unify_var n typ = unify ctxt (lkp n) typ in
  let unify_imm c = match c with
    | IInt _ -> ();
    | IVar v -> unify_var v `Int
  in
  match e with
  | EVar v -> lkp v
  | EInt _ -> `Int
  | Unit -> `Unit
  | Cond (v,e1,e2) ->
    unify_var v `Int;
    let t1 = process_expr ctxt e1 in
    let t2 = process_expr ctxt e2 in
    unify ctxt t1 t2; t1
  | Seq (e1,e2) ->
    process_expr ctxt e1 |> ignore;
    process_expr ctxt e2
  | Assign (v1,IVar v2) ->
    unify_var v1 `IntRef;
    unify_var v2 `Int;
    `Unit
  | Assign (v1,IInt _) ->
    unify_var v1 `IntRef; `Unit
  | Alias (v1, v2) ->
    unify_var v1 `IntRef;
    unify_var v2 `IntRef;
    `Unit
  | Assert { rop1; rop2; _ } ->
    unify_imm rop1;
    unify_imm rop2;
    `Unit
  | ECall c -> process_call lkp ctxt c
  | Let (x,lhs,expr) ->
    let v_type =
      match lhs with
      | Var v -> lkp v
      | Const _ -> `Int
      | Mkref (RNone | RInt _) -> `IntRef
      | Mkref (RVar v) -> unify_var v `Int; `IntRef
      | Deref v -> unify_var v `IntRef; `Int
      | Call c -> process_call lkp ctxt c
      | Plus (v1, v2) ->
        unify_imm v1;
        unify_imm v2;
        `Int
      | Nondet -> `Int
    in
    process_expr { ctxt with tyenv = StringMap.add x v_type ctxt.tyenv } expr

let constrain_fn uf fenv resolv ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let ctxt =  { uf; fenv; tyenv; resolv } in
  let out_type = process_expr ctxt body in
  unify ctxt out_type (`Var (StringMap.find name fenv).ret_type_v)

let typecheck_prog (fns,body) =
  let resolv = Hashtbl.create 10 in
  let uf = UnionFind.mk (fun ~parent ~child ->
      if Hashtbl.mem resolv child then
        Hashtbl.add resolv parent (Hashtbl.find resolv child)
      else ()
    ) in
  let fenv : funenv = make_fenv uf fns in
  List.iter (fun fn_def ->
    constrain_fn uf fenv resolv fn_def
  ) fns;
  process_expr {
    resolv; uf; fenv; tyenv = StringMap.empty
  } body |> ignore;
  let get_soln = force_resolve uf resolv in
  List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
  ) StringMap.empty fns

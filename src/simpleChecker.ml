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
type c_typ = [
  | `Int
  | `Ref of int
]

type typ = [
  c_typ
  | `Var of int
]

type funtyp_v = {
  arg_types_v: int list;
  ret_type_v: int
}

module SM = StringMap
module SS = Set.Make(String)

type funenv = funtyp_v SM.t
type tyenv = typ SM.t

type record_types = {
  rec_of_field: (string,int) Hashtbl.t;
  fields_of_rec: (int,SS.t) Hashtbl.t;
  type_of_field: (string,int) Hashtbl.t
}

type fn_ctxt = {
  uf: UnionFind.t;
  resolv: (int,typ) Hashtbl.t;
  record_t: record_types;
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
  | `Var v ->
    let id = UnionFind.find uf v in
    if Hashtbl.mem resolv id then
      (Hashtbl.find resolv id :> typ)
    else (`Var id)
  | _ -> r

let force_resolve _t_record uf resolv t : r_typ =
  match resolve_type uf resolv t with
  | `Int -> `Int
  | _ -> failwith "Unconstrained value"

let resolve ctxt (r: typ) =
  resolve_type ctxt.uf ctxt.resolv r

let unify ctxt t1 t2 =
  let ty_assign v ty = Hashtbl.add ctxt.resolv v ty in
  match (resolve ctxt t1, resolve ctxt t2) with
  | (`Var v1, `Var v2) -> UnionFind.union ctxt.uf v1 v2
  | (`Var v1, (#c_typ as ct))
  | (#c_typ as ct, `Var v1) ->
    ty_assign v1 ct
  | (`Ref r1,`Ref r2) ->
    if r1 <> r2 then
      failwith "ill-typed"
    else
      ()
  | (t1,t2) when t1 = t2 -> ()
  | _ -> failwith "Ill-typed"

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
  let rec_of_field f =
    `Ref (Hashtbl.find ctxt.record_t.rec_of_field f)
  in
  let field_type f =
    `Var (Hashtbl.find ctxt.record_t.type_of_field f)
  in
  let unify_record v f =
    unify_var v @@ rec_of_field f
  in
  let unify_field f t =
    unify ctxt t @@ field_type f
  in
  match e with
  | EVar v -> lkp v
  | Cond (_,v,e1,e2) ->
    unify_var v `Int;
    let t1 = process_expr ctxt e1 in
    let t2 = process_expr ctxt e2 in
    unify ctxt t1 t2; t1
  | Seq (e1,e2) ->
    process_expr ctxt e1 |> ignore;
    process_expr ctxt e2
  | Assign (v1,f,IInt _,e) ->
    unify_record v1 f;
    unify_field f `Int;
    process_expr ctxt e
  | Assign (v1,f,IVar v2,e) ->
    unify_record v1 f;
    unify_field f @@ lkp v2;
    process_expr ctxt e
  | Alias (_,v1, v2,e) ->
    unify ctxt (lkp v1) (lkp v2);
    process_expr ctxt e
  | Assert ({ rop1; rop2; _ },e) ->
    unify_imm rop1;
    unify_imm rop2;
    process_expr ctxt e
  | Let (_id,x,lhs,expr) ->
    let v_type =
      match lhs with
      | Var v -> lkp v
      | Const _ -> `Int
      | Mkref l ->
        List.iter (fun (k,i) ->
            match i with
            | RNone
            | RInt _ -> unify_field k `Int
            | RVar v -> unify_field k @@ lkp v
          ) l;
        rec_of_field @@ fst @@ List.hd l
      | Field (v,f) ->
        unify_record v f;
        field_type f
      | Call c -> process_call lkp ctxt c
      | Nondet -> `Int
    in
    process_expr { ctxt with tyenv = StringMap.add x v_type ctxt.tyenv } expr

let constrain_fn uf fenv resolv record_t ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let ctxt =  { uf; fenv; tyenv; resolv; record_t } in
  let out_type = process_expr ctxt body in
  unify ctxt out_type (`Var (StringMap.find name fenv).ret_type_v)

let add_fields s ctxt =
  let found = SS.fold (fun f stat ->
    let new_cont =
      match SM.mem f ctxt,stat with
      | f,None -> Some f
      | f,Some f' when f <> f' -> failwith "Inconsistent fields"
      | f,Some f' when f = f' -> stat
      | _ -> assert false
    in
    new_cont
    ) s None in
  match found with
  | None -> failwith "empty record"
  | Some true when not (SM.mem (SS.min_elt s) ctxt) ->
    failwith "Inconsisent fields"
  | Some true ->
    let curr_set = ctxt |> SM.find @@ SS.min_elt s in
    if SS.equal curr_set s then
      ctxt
    else
      failwith "Inconsistent fields"
  | Some false -> SM.add (SS.min_elt s) s ctxt

let process_rec kv_list ctxt =
  let (ss: SS.t) = List.map fst kv_list |> SS.of_list in
  add_fields ss ctxt

let rec compute_f e ctxt =
  match e with
  | EVar _ -> ctxt
    
  | Seq(e1,e2)
  | Cond (_, _, e1, e2) ->
    ctxt
    |> compute_f e1
    |> compute_f e2

  | Let (_,_,Mkref r,e) ->
    process_rec r ctxt
    |> compute_f e
  | Let (_,_,_,e) ->
    compute_f e ctxt
  | Alias (_,_,_,e)
  | Assign (_,_,_,e)
  | Assert (_,e) ->
    compute_f e ctxt

let typecheck_prog _intr_types (fns,body) =
  let rec_ctxt = List.fold_left (fun ctxt {body; _ } ->
      compute_f body ctxt
    ) SM.empty fns
    |> compute_f body
  in
  let (resolv : (int,typ) Hashtbl.t) = Hashtbl.create 10 in
  let uf = UnionFind.mk (fun ~parent ~child ->
      if Hashtbl.mem resolv child then
        Hashtbl.add resolv parent (Hashtbl.find resolv child)
      else ()
    ) in
  let record_t =
    let rec_of_field = Hashtbl.create 10 in
    let fields_of_rec = Hashtbl.create 10 in
    let type_of_field = Hashtbl.create 10 in
    let i = ref 0 in
    SM.iter (fun _ ss ->
      let r_type = !i in
      incr i;
      SS.iter (fun field ->
        let v_type = UnionFind.new_node uf in
        Hashtbl.add rec_of_field field r_type;
        Hashtbl.add type_of_field field v_type;
      ) ss;
      Hashtbl.add fields_of_rec r_type ss
    ) rec_ctxt;
    { rec_of_field; fields_of_rec; type_of_field }
  in
  let fenv_ : funenv = make_fenv uf fns in
  let fenv =
    let _lift_type t =
      let n_id = UnionFind.new_node uf in
      Hashtbl.add resolv n_id t;
      n_id
    in
    (*StringMap.fold (fun k { arg_types; ret_type } ->
      StringMap.add k {
        arg_types_v = List.map lift_type arg_types;
        ret_type_v = lift_type ret_type;
      }
       ) intr_types fenv_*)
    fenv_
  in
  List.iter (constrain_fn uf fenv resolv record_t) fns;
  process_expr {
    resolv; uf; fenv; tyenv = StringMap.empty; record_t
  } body |> ignore;
  let get_soln = force_resolve record_t uf resolv in
  List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
  ) StringMap.empty fns

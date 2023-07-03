(*

SimpleChecker runs a standard HM style type inference algorithm. We have a partial resolution
map, which takes type variables to partially refined type constructors (ints, arrays, etc.), along
with the standard union find data structure for type variables.

To handle recursive types through references, we treat every occurrence
of a reference type as a fresh, unknown type. These are represented
by TyCons.t, i.e., type constructors. We maintain a separate union
find data structure for type constructors; intuitively, if two type constructors
(aka reference types) are unioned, then both types are reference types with identical
contents. As a consequence, during unification,
if two type constructors are equal, then we have two identical types, and can stop recursively
unifying types (this prevents divergence when unifying recursive types). We also maintain a separate
resolution map, which takes type constructors to inference types (i.e., type variables or partially
refined type constructors). Similarly, indirecting through type constructors makes detecting recursive
types extremely easy; if a type constructor X is reachable from the contents of X, then we have a recursive
type. (Note all other recursion is forbidden).
*)

open Ast
open SimpleTypes
open Sexplib.Std

type funtyp_v = {
  arg_types_v: int list;
  ret_type_v: int
}

let rec string_of_typ = function
  | `Var i -> Printf.sprintf "'%d" i
  | `Ref t -> Printf.sprintf "ref %s" @@ string_of_typ t
  | `Int -> "int"
  | `Tuple pl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map string_of_typ pl
  | `Array t' -> Printf.sprintf "[%s]" @@ string_of_typ t'
  | `IntList -> "int list"
[@@ocaml.warning "-32"]


type 'a c_typ = [
  | `Int
  | `Ref of 'a
  | `Tuple of 'a list
  | `Array of 'a
  | `IntList
] [@@deriving sexp]

type typ = [
  typ c_typ
| `Var of int
] [@@deriving sexp]

type refined_typ = typ c_typ

module SM = StringMap
module StringSet = Std.StringSet

type funenv = funtyp_v SM.t
let _sexp_of_tyenv = SM.sexp_of_t ~v:sexp_of_typ
type tyenv = typ SM.t

type resolv_map = (int,typ c_typ) Hashtbl.t

let _sexp_of_resolv_map r = Hashtbl.fold (fun k v acc ->
    (k,v)::acc
  ) r [] |> [%sexp_of: (int * typ) list]

(* A tuple constraint delays some unification until the rest of type checking is complete.
   These constraints arise from aliasing constraints which can constrain a specific type
   at a particular index within a tuple. At the time this constraint is generated, we may not
   know the full size of the tuple, and currently we have no type representation for "a tuple of at least length n".

   Instead, if the tuple size is not yet known, we save a tuple constraint, which
   consists of the type variable (var) representing the tuple, the index (ind), and the
   type variable to unify with type at ind (unif).
   After the rest of type inference is completed, we resolve var, and (assuming it has been properly
   refined to a concrete length tuple) perform the unification with unif at ind.
*)
type tuple_cons = {var: int; ind: int; unif: int; loc: Lexing.position}

type sub_ctxt = {
  uf: UnionFind.t;
  resolv: resolv_map;
  fn_name : string;
}

(* Results accumulated during type inference: the tuple constraints (explained above), the read and write
   pointer operations, and the let types *)
type side_results = {
  t_cons: tuple_cons list;
  let_types: typ Std.IntMap.t; (* let_types gives the type of the RHS of every let expression (by id). This is used
                                  to know what type to give a null constant *)
  match_bindings: (string * typ) list Std.IntMap.t; (* match_binded gives binding information in match statement *)
}

module SideAnalysis = struct
  type results = {
    let_types:  SimpleTypes.r_typ Std.IntMap.t;
    match_bindings: (string * SimpleTypes.r_typ) list Std.IntMap.t;
  }
end

type simple_results = SimpleTypes.funtyp StringMap.t * SideAnalysis.results

type fn_ctxt = {
  sub: sub_ctxt;
  fenv: funenv;
  tyenv: tyenv;
}

(* Abstracts a simple type into an inference type (used to give types to instrinsics) *)
let abstract_type t =
  let rec loop = function
    | `TVar _ -> failwith "Not supported"
    | `Ref t -> `Ref ((loop t) :> typ)
    | `Int -> `Int
    | `Tuple tl ->
      `Tuple (List.map loop tl |> List.map [%cast: typ])
    | `Array t -> `Array ((loop (t :> SimpleTypes.r_typ)) : refined_typ :> typ)
    | `IntList -> `IntList
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
    failwith ("variable shadowing: " ^ v)
  else
    { ctxt with tyenv = StringMap.add v t ctxt.tyenv }

(* Unification related functions *)

(* For type variables or type constructors, find the representative id as recorded in the corresponding UF) *)
let canonicalize sub = function
  | `Var v -> `Var (UnionFind.find sub.uf v)
  | t' -> t'

let rec occurs_check sub v (t2: typ) =
  match canonicalize sub t2 with
  | `Var v' when v' = v -> failwith "Malformed recursive type"
  | `Tuple tl -> List.iter (occurs_check sub v) tl
  | `Array t' -> occurs_check sub v t'
  | `Ref t -> occurs_check sub v t
  | `IntList
  | `Var _
  | `Int -> ()

let assign sub var t =
  occurs_check sub var (t :> typ);
  Hashtbl.add sub.resolv var t

(* unify and unify_tycons are mutually recursive, the former unifies types (typ) and the
   latter unifies reference type constructors *)
let rec unify ~loc sub_ctxt t1 t2 =
  (* unfold (despite the terribly misleading name) doesn't unfold recursive types,
     but rather "unfolds" type variables into whatever the current resolution is.
     It does this by finding the representative variable, and then looking up the
     current partial resolution in the resolv map, or simply returns the variable if there is no resolution *)
  let unfold t1 =
    match canonicalize sub_ctxt t1 with
    | `Var v -> Hashtbl.find_opt sub_ctxt.resolv v
      |> Option.map [%cast: typ]
      |> Option.value ~default:(`Var v)
    | _ -> t1
  in
  let raise_ill_typed_error t1 t2 =
    Locations.raise_errorf ~loc
              "Ill-typed; in %s could not unify %s and %s"
              sub_ctxt.fn_name
              (string_of_typ t1)
              (string_of_typ t2)
  in
  match unfold t1,(unfold t2) with
  | `Var v1,`Var v2 ->
    UnionFind.union sub_ctxt.uf v1 v2
  (* set partial resolution *)
  | `Var v1,(#refined_typ as t)
  | (#refined_typ as t),`Var v1 -> assign sub_ctxt v1 t
  | `Int,`Int -> ()
  (* structural recursion *)
  | (`Tuple tl1 as t1'), (`Tuple tl2 as t2') ->
    if List.length tl1 <> List.length tl2 then
      raise_ill_typed_error t1' t2'
    else
      List.iter2 (unify ~loc sub_ctxt) tl1 tl2
  | `Ref t1',`Ref t2' ->
    unify ~loc sub_ctxt t1' t2'
  | `Array t1',`Array t2' ->
    unify ~loc sub_ctxt t1' t2'
  | `IntList,`IntList -> ()
  | t1',t2' ->
    raise_ill_typed_error t1' t2'

module IS = Std.IntSet

(* translates a inference type into a fully concrete simple type. *)
let rec resolve sub k t =
  match canonicalize sub t with
  | `Int -> k `Int
  | `Ref t -> k @@ `Ref (resolve sub (fun t -> t) t)
  | `Tuple tl ->
    List.fold_left (fun k_acc t ->
      (fun l ->
        resolve sub (fun t' ->
          k_acc (t'::l)
        ) t
      )
    )
    (fun l ->
        k @@ `Tuple l
      ) tl []
  | `Var v when not @@ Hashtbl.mem sub.resolv v -> k `Int
  | `Var v ->
    let t' = Hashtbl.find sub.resolv v in
    resolve sub k (t' :> typ)
  | `Array t' ->
    resolve sub (fun t_lift ->
        match t_lift with
        | `Int -> k @@ `Array `Int
        | _ -> failwith "Only integer arrays are supported"
      ) t'
  | `IntList -> k `IntList

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

let rec process_expr ret_type ctxt ((id,loc),e) res_acc =
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
    unify ~loc ctxt.sub (lkp v) @@ `Ref t
  in
  let fresh_var () =
    let t = UnionFind.new_node ctxt.sub.uf in
    `Var t
  in
  let unify t1 t2 =
    unify ~loc ctxt.sub t1 t2
  in
  let record_tcons =
    let open Std.StateMonad in
    let%lm impl tup_var ind pvar acc =
      { acc with t_cons = { var = tup_var; ind; unif = pvar; loc }::acc.t_cons }
    in
    impl
  in
  let save_let ty acc =
    { acc with let_types = Std.IntMap.add id ty acc.let_types }
  in
  let save_match_binding list acc =
    { acc with match_bindings = Std.IntMap.add id list acc.match_bindings }
  in
  let (|&|) (a,r1) b =
    let (a',r2) = b a in
    a',(r1 && r2)
  in
  let (>>) (a,f) b =
    if f then
      Locations.raise_errorf ~loc "Dead code"
    else
      b a
  in
  let unify_imm imm t =
    match imm with
    | IInt _ -> unify `Int t
    | IVar v -> unify_var v t
  in
  match e with
  | Unit -> res_acc,false
  | Cond (v,e1,e2) ->
    unify_var v `Int;
    process_expr ret_type ctxt e1 res_acc
    |&| process_expr ret_type ctxt e2
  | NCond (v,e1,e2) ->
    unify_ref v @@ fresh_var ();
    process_expr ret_type ctxt e1 res_acc
    |&| process_expr ret_type ctxt e2
  | Seq (e1,e2) ->
    process_expr ret_type ctxt e1 res_acc
    >> process_expr ret_type ctxt e2
  | Assign (v1,IInt _,e) ->
    unify_ref v1 @@ `Int;
    process_expr ret_type ctxt e res_acc
  | Assign (v1,IVar v2,e) ->
    unify_var v1 @@ `Ref (lkp v2);
    process_expr ret_type ctxt e res_acc
  | Update (v1,ind,u,e) ->
    let d = fresh_var () in
    unify_var v1 @@ `Array d;
    unify_var ind `Int;
    unify_var u @@ d;
    process_expr ret_type ctxt e res_acc
  | Alias (ap1, ap2 ,e) ->
    let fresh_node () = UnionFind.new_node ctxt.sub.uf in
    let find (ap : Paths.concr_ap) =
      let open Paths in
      let open Std.StateMonad in
      let (root, steps, suff) = (ap :> root * steps list * suff) in
      match root,suff with
      | Var v,`None ->
        let rec find_loop tau s =
          match s with
          | [] ->
            unify_var v tau;
            return ()
          | `Deref::rest ->
            let ty = `Ref tau in
            find_loop ty rest
          | `Proj i::rest ->
            let tuple_v = fresh_node () in
            let content_v = fresh_node () in
            unify (`Var content_v) tau;
            record_tcons tuple_v i content_v >>
            find_loop (`Var tuple_v) rest
        in
        let aliased_type = fresh_var () in
        let%bind () = find_loop aliased_type steps in
        return aliased_type
      | _,_ -> assert false
    in
    let res_acc,t1 = find ap1 res_acc in
    let res_acc,t2 = find ap2 res_acc in
    unify t1 t2;
    process_expr ret_type ctxt e res_acc
  | Assert ({ rop1; rop2; _ },e) ->
    unify_imm rop1 `Int;
    unify_imm rop2 `Int;
    process_expr ret_type ctxt e res_acc
  | Fail -> res_acc,true
  | Let (PVar v,Mkref (RVar v'),expr) ->
    process_expr ret_type (add_var v (`Ref (lkp v')) ctxt) expr @@ save_let (`Ref (lkp v')) res_acc
  | Let (p,lhs,expr) ->
    let res_acc',v_type =
      let same t = res_acc,t in
      match lhs with
      | Var v -> same @@ lkp v
      | Const _ -> same `Int
      | Mkref i -> same @@ begin
          match i with
          | RNone
          | RInt _ -> `Ref `Int
          | RVar v -> `Ref (lkp v)
        end
      | Call c -> same @@ process_call ~loc lkp ctxt c
      | Nondet _ -> same `Int
      | LengthOf v ->
        let tv = fresh_var () in
        unify_var v @@ `Array tv;
        same @@ `Int
      | Deref p ->
        let tv = fresh_var () in
        unify_var p @@ `Ref tv;
        res_acc,tv
      | Null -> same @@ `Ref( fresh_var ())
      | Tuple tl ->
        let _ = List.fold_left (fun acc r ->
            match r with
            | RInt _
            | RNone -> acc
            | RVar v ->
              if StringSet.mem v acc then
                Locations.raise_errorf ~loc "Duplicate variables in tuple constructor"
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
      | Cons _
      | Nil -> same `IntList
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
    process_expr ret_type ctxt' expr @@ save_let v_type res_acc'
  | Return v -> begin
      match ret_type with
      | None -> Locations.raise_errorf ~loc "Returned %s in main expression" v
      | Some ty ->
        let t = lkp v in
        unify t ty;
        res_acc,true
    end
  | Match (e1, e2, h, r, e3) ->
    let v1 =
      match e1 with
        Var v -> v
      | _ -> Locations.raise_errorf ~loc "Not implemented"
    in
    unify_var v1 `IntList;
    (* No need a constraint to be the return type of e2 and e3 are the same because they share the "ret_type". *)
    let acc1, b1 = process_expr ret_type ctxt e2 res_acc in
    let acc2, b2 = process_expr ret_type (add_var h `Int (add_var r (`Ref `IntList) ctxt)) e3 @@ save_match_binding [(h, `Int); (r, `Ref `IntList)] acc1 in
    acc2, b1 && b2

let constrain_fn sub fenv acc ({ name; body; _ } as fn) =
  let tyenv = init_tyenv fenv fn in
  let ctxt =  { sub = { sub with fn_name = name }; fenv; tyenv  } in
  let acc',_ = process_expr (Option.some @@ `Var (StringMap.find name fenv).ret_type_v) ctxt body acc in
  acc'

let typecheck_prog intr_types (fns,body) =
  let (resolv : (int,refined_typ) Hashtbl.t) = Hashtbl.create 10 in
  let uf = UnionFind.mk () in
  let sub = {
    uf; resolv; fn_name = "";
  } in
  let fenv_ : funenv = make_fenv uf fns in
  let fenv =
    let lift_const t =
      let t_id = UnionFind.new_node uf in
      Hashtbl.add resolv t_id @@ abstract_type t;
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
      let_types = Std.IntMap.empty;
      match_bindings = Std.IntMap.empty;
    } fns
  in
  let (acc',_) = process_expr None {
    sub = { sub with fn_name = "<main>" }; fenv; tyenv = StringMap.empty;
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
    | Some t' -> Locations.raise_errorf ~loc "Ill-typed: expected tuple, got %s" @@ string_of_typ (t' :> typ)
  ) acc'.t_cons;
  let get_soln = resolve sub (fun t -> t) in
  let rec get_soln_with_var_name = function
    | [] -> []
    | (var, ty) :: r -> (var, get_soln ty) :: get_soln_with_var_name r
  in
  (List.fold_left (fun acc { name; _ } ->
    let { arg_types_v; ret_type_v } = StringMap.find name fenv in
    let arg_types = List.map get_soln @@ List.map (fun x -> `Var x) arg_types_v in
    let ret_type = get_soln @@ `Var ret_type_v in
    StringMap.add name { arg_types; ret_type } acc
   ) StringMap.empty fns),SideAnalysis.(
    { let_types = Std.IntMap.map get_soln acc'.let_types;
      match_bindings = Std.IntMap.map get_soln_with_var_name acc'.match_bindings;
    })

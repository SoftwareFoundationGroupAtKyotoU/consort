open Ast

open Sexplib.Std

open Std
open Std.StateMonad
open SimpleTypes
    
module SM = StringMap
module SS = StringSet
module P = Paths
module OI = OwnershipInference
module RT = RefinementTypes

open (val Log.located ~where:"FLOW" : Log.LocatedD) [@@ocaml.warning "-33"]

type z3_types =
  | ZBool
  | ZInt [@@deriving sexp]

type relation_source =
  | Expr of int
  | Fun of string * [`In | `Out]
  | FunMu of string * [`In | `Out] * P.concr_ap
  | ExprMu of int * P.concr_ap * [`Null | `Join | `Flow]
  | AliasUnfold of int
  | Start [@@deriving sexp]

type flow =
  | Havoc of P.concr_ap
  | Copy of P.concr_ap * P.concr_ap
  | Const of P.concr_ap * int
  | NullConst of P.concr_ap * bool

type relation = string * (P.concr_ap * z3_types) list * relation_source [@@deriving sexp]

type concr_arg =
  | Ap of P.concr_ap
  | BConst of bool
  | IConst of int
  | NondetChoice of concr_arg list
  | KeyedChoice of P.concr_ap * concr_arg * concr_arg [@@deriving sexp]

type clause =
  | PRelation of relation * ((P.concr_ap * concr_arg) list) * int option
  | Relation of (concr_arg,concr_arg) RT.relation * z3_types
  | NamedRel of string * (concr_arg list)
  | NullCons of concr_arg * concr_arg

type fltype = [
  | `IntArray
  | `Ref of bool * fltype
  | `Int
  | `Tuple of fltype list
  | `Mu of fltype
  | `TVar
]

let rec fltype_to_string = function
  | `IntArray -> "[int]"
  | `Mu t -> Printf.sprintf "(%s %s.%s)" Greek.mu Greek.alpha @@ fltype_to_string t
  | `Ref (_,t) -> Printf.sprintf "%s ref" @@ fltype_to_string t
  | `Int -> "int"
  | `Tuple tl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map fltype_to_string tl
  | `TVar -> Greek.alpha

type funtype = fltype _funtyp

type recursive_ref_map = relation P.PathMap.t

type function_info = {
  in_rel : relation;
  out_rel : relation;
  f_type: funtype;
  in_recursive_rel: recursive_ref_map;
  out_recursive_rel : recursive_ref_map;
}

type state_snapshot = {
  mu_relations : recursive_ref_map;
  gamma : (string * fltype) list;
  relation : relation
}

type ctxt = {
  relations: relation list;
  impl: (clause list * clause) list;
  o_hints: float OI.ownership_ops;
  fenv: function_info SM.t;
  curr_fun : string option;
  let_types: fltype IntMap.t;
  bif_types : RefinementTypes.funtype SM.t;
  havoc_set : P.PathSet.t;
  unfold_iso: IntSet.t;
  fold_iso: IntSet.t;
  recursive_rel : recursive_ref_map;
  snapshots : state_snapshot IntMap.t
}

let rec unfold_fltype subst = function
  | `TVar -> subst
  | `Mu _ -> assert false
  | `Int -> `Int
  | `Ref (false,t) -> `Ref (false,unfold_fltype subst t)
  | `Ref (true,_) -> failwith "Already unfolded ref under a mu binder?!?!?"
  | `Tuple tl -> `Tuple (List.map (unfold_fltype subst) tl)
  | `IntArray -> `IntArray

let rec deep_type_normalization = function
  | `Mu (`Ref (false,t)) ->
    `Ref (true,unfold_fltype (`Mu (`Ref (false,t))) t)
  | `Mu (`Ref (true,_)) -> failwith "broken invariant"
  | `Mu _ -> assert false
  | `Int -> `Int
  | `Tuple tl -> `Tuple (List.map deep_type_normalization tl)
  | `Ref (b,t) -> `Ref (b, deep_type_normalization t)
  | `IntArray -> `IntArray
  | `TVar -> assert false

let rec simple_to_fltype ?tvar = function
  | `Mu (id,t) ->
    assert (tvar = None);
    `Mu (simple_to_fltype ~tvar:id t)
  | `Int -> `Int
  | `Array `Int -> `IntArray
  | `Ref t -> `Ref (false, simple_to_fltype ?tvar t)
  | `TVar id ->
    assert (Option.map ((=) id) tvar |> Option.value ~default:false);
    `TVar
  | `Tuple tl -> `Tuple (List.map (simple_to_fltype ?tvar) tl)
    
let%lq get_function_type f_name ctxt =
  let { f_type; _ } = StringMap.find f_name ctxt.fenv in
  f_type

let%lq get_in_relation f_name ctxt =
  let { in_rel = ir; _} = StringMap.find f_name ctxt.fenv in
  ir

let%lq get_out_relation f_name ctxt =
  let { out_rel = o_rel; _ } = StringMap.find f_name ctxt.fenv in
  o_rel

let%lq get_function_info f_name ctxt =
  StringMap.find f_name ctxt.fenv

let%lq copy_state ctxt = ctxt

let%lm set_havoc_state havoc_state ctxt = { ctxt with havoc_set = havoc_state }

let%lq get_havoc_state ctxt = ctxt.havoc_set

let%lq get_bound_type e_id ctxt = IntMap.find e_id ctxt.let_types

let mk_relation lhs op rhs = RT.({
    rel_op1 = lhs;
    rel_cond = op;
    rel_op2 = rhs
  })

let rel ~ty k = Relation (k,ty)

(* TODO: make this function actually useful... *)
let path_type p = if P.is_nullity p then ZBool else ZInt

let%lm add_assert op1 cond op2 curr_relation ctxt =
  let ante = [ PRelation (curr_relation,[],None) ] in
  let relation = rel ~ty:ZInt @@ mk_relation op1 cond op2 in
  { ctxt with impl = (ante,relation)::ctxt.impl }

let add_assert_cond assert_cond curr_relation =
  let lift_to_imm = function
    | IVar v -> Ap (P.var v)
    | IInt i -> IConst i
  in
  add_assert
    (lift_to_imm assert_cond.rop1)
    assert_cond.cond
    (lift_to_imm assert_cond.rop2)
    curr_relation

let rec havoc_oracle ctxt ml p =
  Log.debug ~src:"FLOW-OWN" !"Looking for %{P} @ %{sexp:OI.magic_loc}" p ml;
  let from_path p_ =
    let o = OI.GenMap.find (ml,p_) ctxt.o_hints.OI.gen in
    o = 0.0
  in
  match P.tail p with
  | Some `Deref
  | Some `Ind
  | Some `Elem -> from_path @@ P.parent p
  | Some _ -> havoc_oracle ctxt ml @@ P.parent p
  | None -> false

let%lq split_oracle sl ctxt =
  let from_path p =
    Log.debug ~src:"FLOW-OWN" !"Splitting %{P} @ %{sexp:OI.split_loc}" p sl;
    let (f1,f2) = OI.SplitMap.find (sl,p) ctxt.o_hints.OI.splits in
    let to_flag b = if b then `Havoc else `Stable in
    (to_flag (f1 = 0.0), to_flag (f2 = 0.0))
  in
  let rec loop p1 p2 =
    match (P.tail p1),(P.tail p2) with
    | None,_ -> (`Trivial,`Trivial)
    | _,None -> (`Trivial, `Trivial)
    | Some a,Some b ->
      let () =  assert (a = b) in
      if a = `Deref || a = `Ind || a = `Elem then
        from_path @@ P.parent p1
      else
        loop (P.parent p1) (P.parent p2)
  in
  loop
    
let%lq gen_for_alias e_id ctxt =
  havoc_oracle ctxt (OI.MAlias e_id)

let%lq gen_oracle ml ctxt =
  havoc_oracle ctxt ml

let rec lift_refinement ?(map=Fun.id) ?nu_arg =
  let lift_symbolic_ap = function
    | `Sym _ -> assert false
    | `Concr cap -> map cap
  in
  let lift_symbolic_imm = function
    | RT.RConst i -> IConst i
    | RT.RAp p -> Ap (lift_symbolic_ap p)
  in
  RT.(function
  | Top -> []
  | And (r1, r2) -> lift_refinement ~map ?nu_arg r1 @ lift_refinement ~map ?nu_arg r2
  | ConstEq i ->
    [ rel ~ty:ZInt @@ mk_relation (Ap (Option.get nu_arg)) "=" (IConst i) ]
  | Relation r when r.rel_op1 = Nu ->
    [ rel ~ty:ZInt { r with rel_op1 = Ap (Option.get nu_arg); rel_op2 = lift_symbolic_imm r.rel_op2 } ]
  | Relation ({ rel_op1 = RImm i; _ } as r) ->
    [ rel ~ty:ZInt { r with rel_op1 = (lift_symbolic_imm i); rel_op2 = lift_symbolic_imm r.rel_op2 } ]
  | NamedPred (nm,sym_names) ->
    let nu_arg = Option.get nu_arg in
    let named_args = List.map lift_symbolic_ap sym_names in
    let val_args = List.map (fun l -> Ap l) @@ nu_arg::named_args in
    [ NamedRel (nm,val_args) ]
  | _ -> failwith "Refinement form not supported")

let path_simple_type tyenv path =
  let rec loop (path: P.path) k =
    match P.tail path with
    | None -> begin
        match (path : P.path :> P.root * 'a * 'b) with
        | (P.Var v,_,_) -> k @@ List.assoc v tyenv
        | _ -> failwith "not supported"
      end
    | Some `Deref -> 
        loop (P.parent path) (function
        | `Ref (_,t) -> k t
        | t -> failwith @@ Printf.sprintf "Unexpected simple type %s for path %s" (fltype_to_string t) (P.to_z3_ident path)
        )
    | Some (`Proj i) ->
      loop (P.parent path) (function
        | `Tuple tl -> List.nth tl i
        | _ -> assert false
        )
    | _ -> failwith "Not supported"
  in
  loop path (fun i -> i)

let is_null_flag = true
let is_nonnull_flag = false

let null_pre (_,args,_) subst =
  let subst_ap p =
    if List.mem_assoc p subst then
      List.assoc p subst
    else
      Ap p
  in
  let rec parent_null_loop p =
    match P.tail p with
    | None -> None
    | Some `Deref ->
      Some (P.to_null @@ P.parent p)
    | Some _ -> parent_null_loop @@ P.parent p
  in
  List.filter_map (fun (p,_) ->
    if not @@ P.is_nullity p then
      None
    else
      P.parent p
      |> parent_null_loop
      |> Option.map (fun parent ->
          (NullCons (subst_ap parent, subst_ap p))
        )
  ) args

let to_havoc d = Printf.sprintf "havoc!%d!%s" d 

let havoc_ap d p =
  P.map_root (to_havoc d) @@
  if P.is_template p then
     P.root_at ~child:p ~parent:(P.var "$tmp")
  else
    p

let to_pass_ap = P.map_root (fun s -> "pass!" ^ s)

let lift_copy (s,d) = (s, Ap d)

let%lm add_implication ante conseq ctxt =
  {ctxt with impl = (ante,conseq)::ctxt.impl }

let flow_to_subst i = function
  | Havoc p -> p,Ap (havoc_ap i p)
  | Const (p,c) -> (p,IConst c)
  | Copy (p1,p2) -> (p2,Ap p1)
  | NullConst (p,b) -> (p,BConst b)

let%lm add_relation_flow ?out_ctxt ?(pre=[]) subst in_rel out_rel ctxt =
  let lifted_subst = List.mapi flow_to_subst subst in
  let ante = PRelation (in_rel,[],None)::pre in
  let conseq = PRelation (out_rel,lifted_subst,out_ctxt) in
  {
    ctxt with impl = ((ante,conseq)::ctxt.impl)
  }

let type_to_paths ?(pre=false) root (ty: fltype) =
  let add_path pre under_ref under_mu acc p =
    let paths =
        (if under_ref && not under_mu && pre then
           [P.pre p] else []) @
        [p]
    in
    paths @ acc
  in
  let rec loop under_ref under_mu acc p = function
    | `Int -> add_path pre under_ref under_mu acc p
    | `Ref (_,t) ->
      let acc = add_path pre under_ref under_mu acc (P.to_null p) in
      loop true under_mu acc (P.deref p) t
    | `Tuple tl ->
      fold_lefti (fun i acc t ->
          loop under_ref under_mu acc (P.t_ind p i) t
        ) acc tl
    | `IntArray ->
      List.fold_left (add_path false under_ref under_mu) acc [(P.len p);(P.ind p);(P.elem p)]
    | `Mu t -> loop under_ref true acc p t
    | `TVar -> acc
  in
  loop false false [] root ty

let path_step k p = match k with
  | `Ind -> P.ind p
  | `Length -> P.len p
  | `Elem -> P.elem p
  | `Tuple i -> P.t_ind p i
  | `Ref -> P.deref p
  | `Null -> P.to_null p
  (* pseudo-path elements *)
  | `Mu -> p
  | `Summ -> p
  | `Array -> p

let rec walk_type ty step f st acc =
  let continue ~acc mst k =
    match mst with
    | `K f_ -> f_ ty acc
    | `ContWith (f,st) -> let acc = f ty acc in k st acc
    | `Cont st -> k st acc
  in
  match ty with
  | `Int -> f st acc
  | `Ref (false, t) ->
    let mst = step `Null st in
    continue ~acc mst (fun st' acc ->
      let acc = f st' acc in
      let mst = step `Ref st in
      continue ~acc mst (walk_type t step f)
    )
  | `Ref (true,t) ->
    let mst = step `Null st in
    continue ~acc mst (fun st' acc ->
      let acc = f st' acc in
      let mst = step `Summ st in
      continue ~acc mst (fun st' acc ->
        let mst = step `Ref st' in
        continue ~acc mst (walk_type t step f)
      )
    )
  | `Tuple tl ->
    fold_lefti (fun i acc t ->
        let mst = step (`Tuple i) st in
        continue ~acc mst (walk_type t step f)
      ) acc tl
  | `TVar -> acc
  | `Mu t ->
    let mst = step `Mu st in
    continue ~acc mst (walk_type t step f)
  | `IntArray ->
    let mst = step `Length st in
    continue ~acc mst (fun st' acc ->
      let acc = f st' acc in
      let mst = step `Array st in
      continue ~acc mst (fun st acc ->
        let mst = step `Ind st in
        continue ~acc mst (fun st' acc ->
          let acc = f st' acc in
          let mst = step `Elem st in
          continue ~acc mst f
        )
      )
    )

let parallel_type_walk in_ap out_ap ty step f st acc =
  walk_type ty (fun k (in_ap,out_ap,st) ->
    let user_step constr kind =
      let mst = step kind (in_ap,out_ap) st in
      match mst with
      | `K f -> `K f
      | `ContWith (f,st) -> `ContWith (f,(constr in_ap, constr out_ap, st))
      | `Cont st -> `Cont (constr in_ap,constr out_ap,st)
      | `ContPath (in_ap,out_ap, st) -> `Cont (in_ap, out_ap, st)
    in
    let parallel_step constr =
      `Cont (constr in_ap, constr out_ap, st)
    in
    match k with
    | `Ref -> user_step P.deref `Ref
    | `Mu -> user_step Fun.id `Mu
    | `Array -> user_step Fun.id `Array
    | `Ind -> parallel_step P.ind
    | `Elem -> parallel_step P.elem
    | `Length -> parallel_step P.len
    | `Tuple i -> parallel_step ((Fun.flip P.t_ind) i)
    | `Null -> parallel_step P.to_null
    | `Summ -> user_step Fun.id `Summ
  ) (fun (in_ap, out_ap, st) acc ->
    f st in_ap out_ap acc
  ) (in_ap, out_ap, st) acc


module RecRelations = struct

  module MuChain = struct
    let to_concr (s,p) =
      Option.fold ~none:s ~some:(fun parent ->
        P.root_at ~child:s ~parent
      ) p

    let step_mu (s,p) =
      assert (p = None);
      (P.template, Some s)

    let get_mu_path (s,p) =
      Option.map (fun p ->
        (s,p)
      ) p

    let raw_stepper k (s,p) = match k with
      | `Mu -> `Cont (step_mu (s,p))
      | _ -> `Cont (path_step k s, p)
  end

  let get_recursive_roots root ty =
    walk_type ty (fun k s ->
      match k with
      | `Summ -> `K (fun ty acc -> (s,ty)::acc)
      | _ -> `Cont (path_step k s)
    ) (fun _ acc -> acc) root []

  let get_mu_binders root ty =
    walk_type ty (fun k s ->
      match k with
      | `Mu -> `K (fun _ acc -> s::acc)
      | _ -> `Cont (path_step k s)
    ) (fun _ acc -> acc) root []

  let mu_transposition_of ~ty path =
    get_mu_binders P.template ty |> List.map (fun binders ->
        P.root_at ~child:path ~parent:binders
      )

  let update_rel_map dst rel =
    P.PathMap.add dst rel

  let set_recursive_rel dst rel ctxt =
    { ctxt with recursive_rel = update_rel_map dst rel ctxt.recursive_rel }

  let recursive_rel_for ~e_id ty dst ctxt =
    let name =
      Printf.sprintf !"%{P}-%d-%s" dst e_id "mu"
    in
    let args = type_to_paths P.template ty |> List.map (fun p -> p, path_type p) in
    let rel = (name, args, ExprMu (e_id, dst, `Flow)) in
    let ctxt = set_recursive_rel dst rel @@ { ctxt with relations = rel :: ctxt.relations } in
    ctxt,rel

  let recursive_havoc_subst ty havoc_paths =
    havoc_paths |> ListMonad.bind (fun p ->
        p::(mu_transposition_of ~ty p)
      ) |> List.mapi (fun i s -> (s, Ap (havoc_ap i s)))

  let impl_with_havoc ?out_shift ~by_havoc ~ante dst_root dst_rel ctxt =
    let havoc_subst =
      P.PathMap.find_opt dst_root by_havoc
      |> Option.map (fun (ty,havoc_paths) ->
          recursive_havoc_subst ty @@ P.PathSet.elements havoc_paths
        )
      |> Option.value ~default:[]
    in
    { ctxt with impl = (ante, PRelation (dst_rel, havoc_subst, out_shift))::ctxt.impl }

  let recursive_rel_with_havoc ~by_havoc ~e_id ~ante dst_root ty (ctxt : ctxt) =
    let ctxt,rel = recursive_rel_for ~e_id ty dst_root ctxt in
    impl_with_havoc ~by_havoc ~ante dst_root rel ctxt

  let%lm null_for_var ~e_id ~ty var ctxt =
    get_recursive_roots (P.var var) ty
    |> List.fold_left (fun ctxt (root,ty) ->
        let args = type_to_paths P.template ty |> List.map (fun p -> p, path_type p) in
        get_mu_binders root ty |> List.fold_left (fun ctxt bind ->
            let name = Printf.sprintf !"null-%d-%{P}-%s" e_id bind "mu" in
            let rel = (name, args, ExprMu (e_id, bind, `Null)) in
            let grounding_subst = List.filter_map (fun (s, p) ->
                match p with
                | ZBool ->
                  let () = assert (P.is_nullity s) in
                  Some (s, BConst is_null_flag)
                | _ -> None
              ) args in
            set_recursive_rel
              bind rel
              { ctxt with
                relations = rel::ctxt.relations;
                impl = ([], PRelation (rel, grounding_subst, None))::ctxt.impl
              }
          ) ctxt
      ) ctxt
end

type copy_spec = {
  direct_copies: (P.concr_ap * P.concr_ap) list;
  weak_copies: (P.concr_ap * P.concr_ap * fltype) list
}

let empty_copy = {
  direct_copies = [];
  weak_copies = [];
}

let add_weak src dst ty cs = {
  cs with weak_copies = (src,dst,ty)::cs.weak_copies
}

let add_direct src dst cs = {
  cs with direct_copies = (src,dst)::cs.direct_copies
}

let ccat a1 a2 = {
  direct_copies = a1.direct_copies @ a2.direct_copies;
  weak_copies = a1.weak_copies @ a2.weak_copies
}

let compute_copies in_ap out_ap ty : copy_spec =
  parallel_type_walk in_ap out_ap ty (fun k (in_ap,out_ap) () ->
    match k with
    | `Summ -> `K (fun ty -> add_weak in_ap out_ap ty)
    | _ -> `Cont ()
  ) (fun () -> add_direct) () empty_copy

let to_copy_stream { direct_copies; weak_copies } =
  let l = List.map (fun (s,d) ->
      s,d,`Direct
    ) direct_copies
  in
  List.fold_left (fun acc (s,d,ty) ->
    parallel_type_walk s d ty (fun k (in_ap,dst_ap) stack ->
      match k with
      | `Mu -> `ContPath (P.template, dst_ap, Some (in_ap, dst_ap))
      | `Summ | `Ref | `Array -> `Cont stack
    ) (fun stack in_ap out_ap acc ->      
      let s = (in_ap, Option.map fst stack) in 
      let concr_in = RecRelations.MuChain.to_concr s in
      let acc = (concr_in, out_ap, `Direct)::acc in
      Option.fold ~none:acc ~some:(fun (in_mu,out_mu) ->
        (concr_in,out_ap, `Mu (in_ap, in_mu,out_mu, ty))::acc
      ) stack
    ) None acc
  ) l weak_copies

let to_mu_copies { weak_copies; _ } =
  ListMonad.bind (fun (s,d,ty) ->
    RecRelations.get_mu_binders P.template ty
    |> List.map (fun st -> 
        (st,
         P.root_at ~child:st ~parent:s,
         P.root_at ~child:st ~parent:d,ty)
      )
  ) weak_copies

let compute_patt_copies path patt ty =
  let rec loop patt path ty acc =
    match patt,ty with
    | PNone,_ -> acc
    | PVar v,`Int ->
      add_direct path (P.var v) acc
    | PVar v,ty ->
      ccat (compute_copies path (P.var v) ty) acc
    | PTuple t,`Tuple tl ->
      fold_left2i (fun i acc p t ->
          loop p (P.t_ind path i) t acc
        ) acc t tl
    | PTuple _,_ -> assert false
  in
  loop patt path ty empty_copy

module Havoc = struct
  type mu_havoc = (fltype * P.PathSet.t) P.PathMap.t

  type havoc_state = {
    havoc: P.PathSet.t;
    stable: P.PathSet.t;
    mu_havoc: mu_havoc
  }

  let empty_havoc_state = {
    havoc = P.PathSet.empty;
    stable = P.PathSet.empty;
    mu_havoc = P.PathMap.empty;
  }

  let add_havoc p f m =
    if f then
      { m with havoc = P.PathSet.add p m.havoc }
    else
      { m with stable = P.PathSet.add p m.stable }

  let add_mu_havoc ~binder ~ty p f m =
    if f then
      { m with mu_havoc =
          P.PathMap.update binder (function
          | None -> Some (ty, P.PathSet.singleton p)
          | Some (ty',set) ->
            let () = assert (ty = ty') in
            Some (ty, P.PathSet.add p set)
          ) m.mu_havoc
      }
    else
      m

  let to_rec_havoc { mu_havoc; _ } = mu_havoc

  let%lm update_null_havoc ~e_id ~ty var ctxt =
    let ref_havoc p = (OI.GenMap.find (OI.MGen e_id, p) ctxt.o_hints.OI.gen) = 0.0 in
    let hstate =
      walk_type ty (fun k (f,p) ->
        let f =
          match k with
          | `Ref | `Array -> ref_havoc p
          | _ -> f
        in
        `Cont (f, path_step k p)
      ) (fun (f, p) acc ->
        add_havoc p f acc
      ) (false, P.var var) empty_havoc_state
    in
    { ctxt with havoc_set = P.PathSet.union hstate.havoc @@ P.PathSet.diff ctxt.havoc_set hstate.stable }
end

module H = Havoc

let augment_havocs flows havoc_set =
  List.filter (fun (p,_) -> not (P.PathSet.mem p havoc_set)) flows |> P.PathSet.fold (fun p acc ->
      (p, Ap (havoc_ap 0 p))::acc
    ) havoc_set

let compute_flows ~sl copies ctxt =
  let _,split_oracle = split_oracle sl ctxt in
  to_copy_stream copies |> List.fold_left (fun (hstate,rename_copy,copy_subst,out_subst) (src,dst,k) ->
      let (h_in,h_out) = split_oracle src dst in
      let add_havoc p f ostate =
        if f = `Trivial then ostate
        else Havoc.add_havoc p (f = `Havoc) ostate
      in
      let hstate = add_havoc src h_in @@ add_havoc dst h_out hstate in
      match k with
      | `Direct -> hstate,rename_copy,copy_subst,(dst, Ap src)::out_subst
      | `Mu (under_mu_path, s, d, ty) ->
        let () =
          assert (h_in <> `Trivial);
          assert (h_out <> `Trivial)
        in
        let hstate =
          Havoc.add_mu_havoc ~binder:s ~ty under_mu_path (h_in = `Havoc) hstate
          |> Havoc.add_mu_havoc ~binder:d ~ty under_mu_path (h_out = `Havoc)
        in
        hstate,(dst, Ap (to_pass_ap src))::rename_copy,(src, Ap dst)::copy_subst, out_subst

    ) (Havoc.empty_havoc_state,[],[],[])

let copy_rel ~by_havoc ~e_id ~ty src_rel dst_root ctxt =
  if P.PathMap.mem dst_root by_havoc then
    RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante:([
      PRelation (src_rel, [], None)
    ]) dst_root ty ctxt
  else
    RecRelations.set_recursive_rel dst_root src_rel ctxt

let%lm apply_copies ?out_rec_rel ~havoc:havoc_flag ~sl ?(flows=[]) ?pre copies in_rel out_rel ctxt =
  let hstate,rename_copy,copy_flows,out_flows = compute_flows ~sl copies ctxt in
  let mu_copies = to_mu_copies copies in
  let havoc_set = ctxt.havoc_set in
  let havoc_set = P.PathSet.union hstate.H.havoc @@ P.PathSet.diff havoc_set hstate.H.stable in
  let applied_havocs = if havoc_flag then havoc_set else hstate.H.havoc in
  let flows = List.mapi flow_to_subst flows in
  let out_flows = augment_havocs (flows @ out_flows) applied_havocs in
  let pre =
    Option.value ~default:[] pre @
      if (List.compare_length_with copy_flows 0) > 0 then
        [
          PRelation(in_rel, rename_copy, None);
          PRelation(in_rel, rename_copy @ copy_flows, None)
        ]
      else
        [ PRelation(in_rel, [], None) ]
  in
  let conseq = PRelation(out_rel, out_flows, None) in
  let ctxt =
    let by_havoc = H.to_rec_havoc hstate in
    List.fold_left (fun ctxt (_,src,dst,ty) ->
      let () =
        assert (P.PathMap.mem src ctxt.recursive_rel);
      in
      let e_id =
        match sl with
        | OI.SRet e_id
        | OI.SBind e_id
        | OI.SCall e_id -> e_id
      in
      let src_rel = P.PathMap.find src ctxt.recursive_rel in
      let ctxt = copy_rel ~by_havoc ~e_id ~ty src_rel src ctxt in
      match out_rec_rel with
      | Some (direct_flow,_) ->
        P.PathMap.find_opt dst direct_flow
        |> Option.fold ~none:ctxt ~some:(fun rel ->
            RecRelations.impl_with_havoc ~by_havoc ~ante:[
              PRelation (src_rel, [], None)
            ] dst rel ctxt
          )
      | None -> copy_rel ~by_havoc ~e_id ~ty src_rel dst ctxt
    ) ctxt mu_copies
  in
  let ctxt =
    match out_rec_rel with
    | None -> ctxt
    | Some (_,extra_rec_flows) ->
      List.fold_left (fun ctxt (src,rel) ->
          let in_rel = P.PathMap.find src ctxt.recursive_rel in
          { ctxt with impl = ([ PRelation(in_rel, [], None)], PRelation (rel, [], None))::ctxt.impl }
        ) ctxt extra_rec_flows
  in
  { ctxt with havoc_set; impl = (pre, conseq)::ctxt.impl }

module IdMap(M: Map.S) : sig
  type t
  val id_map : t
  val find : M.key -> t -> M.key
  val add : M.key -> M.key -> t -> t
  val mem : M.key -> t -> bool
  val empty : t
end = struct
  type t = (M.key M.t) option
  let empty = Some M.empty
  let id_map = None
  let add k v = function
    | None -> failwith "Cannot add to infinite map"
    | Some w -> Some (M.add k v w)

  let q f = fun k -> Option.fold ~none:true ~some:(f k)
  let mem = q M.mem
      
  let l f = fun k -> Option.fold ~none:k ~some:(f k)
  let find = l M.find
end

module PPMap = IdMap(P.PathMap)

module RecursiveRefinements = struct

  type mu_frag = P.path * fltype

  type rooted_mu = {
    hd: mu_frag;
    recurse: mu_frag P.PathMap.t;
  }

  module Subst = struct
    let rec concr_arg_to_string = function
      | Ap p -> P.to_z3_ident p
      | BConst b -> Bool.to_string b
      | IConst i -> string_of_int i
      | NondetChoice l -> List.map concr_arg_to_string l |> String.concat ", " |> Printf.sprintf "{?%s}"
      | KeyedChoice (p,a1,a2) ->
        Printf.sprintf "[? %s %s %s]" (P.to_z3_ident p) (concr_arg_to_string a1) (concr_arg_to_string a2)
        
    let to_string l = List.map (fun (p,a) ->
        Printf.sprintf !"%{P} |-> %s" p @@ concr_arg_to_string a
      ) l |> String.concat "; " |> Printf.sprintf "[ %s ]"
          [@@ocaml.warning "-32"]
  end

  let to_mu_template ty =
    let recurse = walk_type ty (fun k ap ->
      match k with
      | `Summ -> `Cont ap
      | `Mu -> `K (fun ty acc -> (ap,ty)::acc)
      | _ -> `Cont (path_step k ap)
      ) (fun _ acc -> acc) P.template []
    in
    let recurse = List.fold_left (fun acc (p,ty) ->
        P.PathMap.add p (p,ty) acc
      ) P.PathMap.empty recurse
    in
    {
      hd = (P.template, ty);
      recurse
    }

  let root_template_at tmpl path =
    let root_frag (p,ty) =
      (P.root_at ~child:p ~parent:path, ty)
    in
    {
      hd = root_frag tmpl.hd;
      recurse = P.PathMap.map root_frag tmpl.recurse
    }

  let to_multi_subst substs indexed_subst =
    fold_lefti (fun i acc sub_group ->
        let indexed_sub = List.fold_left (fun acc (ind,substs) ->
            List.fold_left (fun acc (s,d) ->
              P.PathMap.update s (fun curr ->
                Some ((ind,d)::(Option.value ~default:[] curr))
              ) acc
            ) acc substs
          ) P.PathMap.empty sub_group in
        let keyed_ap j =
          (P.var @@ Printf.sprintf "star!%d!%d" i j)
        in
        let to_unary_subst sorted =
          match sorted with
          | [] -> assert false
          | l ->
            let l = List.sort (fun (k1,_) (k2,_) ->
                k2 - k1
              ) l
            in
            let (_,hd) = List.hd l in
            let tl = List.tl l in
            fold_lefti (fun i acc (_,ap) ->
              KeyedChoice (keyed_ap i, Ap ap, acc)
            ) (Ap hd) tl
        in
        P.PathMap.fold (fun s dlist acc ->
          (s,to_unary_subst dlist)::acc
        ) indexed_sub acc
      ) (List.map lift_copy substs) indexed_subst
       
  let compute_frag_subst ?(acc=[]) ~skip_ref src_frag dst_frag =
    let ty,src,dst =
      if skip_ref then
        match snd src_frag with
        | `Ref (_,t) -> t,(P.deref @@ fst src_frag),(fst dst_frag)
        | _ -> assert false
      else
        (snd src_frag),fst src_frag,fst dst_frag
    in
    let ty = match ty with
      | `Mu t -> t
      | _ -> ty
    in
    parallel_type_walk src dst ty (fun k _ () ->
      match k with
      | `Mu -> `K (fun _ acc -> acc)
      | `Summ | `Array | `Ref -> `Cont ()
    ) (fun () in_ap out_ap acc ->
      (in_ap, out_ap)::acc
    ) () acc

  let compute_mu_template_subst { hd = (path,ty); _ } =
    parallel_type_walk P.template path ty (fun _ _ () -> `Cont ()) (fun () in_ap out_ap acc ->
      (in_ap, Ap out_ap)::acc
    ) () []

  let compute_mu_multi_subst ?(skip_hd_ref=false) src_templ ~hd:hfrag ~tl:tfrags =
    let subst = compute_frag_subst ~skip_ref:skip_hd_ref src_templ.hd hfrag in
    let indexed_subst = P.PathMap.fold (fun bind_path src_frag acc ->
      let dst_frags = P.PathMap.find bind_path tfrags in
      let sub_group = fold_lefti (fun i acc dst_frag ->
        let s = compute_frag_subst ~skip_ref:false src_frag dst_frag in
        (i,s)::acc
        ) [] dst_frags in
      sub_group::acc
      ) src_templ.recurse []
    in
    to_multi_subst subst indexed_subst

  let compute_mu_subst src_templ ~hd:hfrag ~tl:tfrags =
    let subst = compute_frag_subst ~skip_ref:false src_templ.hd hfrag in
    P.PathMap.fold (fun path src_frag acc ->
      let dst_frag = P.PathMap.find path tfrags in
      compute_frag_subst ~skip_ref:false ~acc src_frag dst_frag
    ) src_templ.recurse subst
    |> List.map lift_copy

  let partial_subst src dst ty =
    parallel_type_walk src dst ty (fun k _ () -> match k with
    | `Mu -> `K (fun _ acc -> acc)
    | _ -> `Cont ()
    ) (fun () in_ap out_ap acc -> (in_ap, out_ap)::acc) () []

  let relation_subst rel subst =
    PRelation (rel, subst, None)

  let unfold_to ~with_havoc ?(out_mapping=PPMap.id_map) ~e_id ref_ty root target in_rel out_rel ctxt =
    let normalize_havoc pset = P.PathSet.filter (fun p ->
        PPMap.mem p out_mapping
      ) pset |> P.PathSet.map (fun p ->
          PPMap.find p out_mapping
        )
    in
    let normalize_ap p =
      if PPMap.mem p out_mapping then
        PPMap.find p out_mapping
      else
        p
    in
    let rec deep_normalize = function
      | Ap p -> Ap (normalize_ap p)
      | BConst c -> BConst c
      | IConst i -> IConst i
      | NondetChoice c -> NondetChoice (List.map deep_normalize c)
      | KeyedChoice (p,a1,a2) ->
        KeyedChoice (normalize_ap p, deep_normalize a1, deep_normalize a2)
    in
    let normalize_subst subst =
      List.map (fun (s,d) ->
        (s, deep_normalize d)
      ) subst
    in

    let cont_ty = match ref_ty with
      | `Ref (_,t) -> t
      | _ -> assert false
    in
        
    let source_path = P.var root in
    let template = to_mu_template ref_ty in
    let source_mu = root_template_at template source_path in
    let target_path = P.var target in

    (* Roughly speaking, we unfold the relation R(hd, tl) as follows:

       R(hd, tl!pass) /\ R(hd, tl) /\ R(hd, tl->tl) /\ hd(tl, tl->tl) => R(hd, tl!pass, hd, tl, tl->tl)
       hd(x,y) => tl(x, y)

       R here encodes a relationship between hd and all tail elements, i.e. elements reachable from the tail pointer of hd.
       hd(x,y) encodes the recursive refinement, i.e., after unfolding, what relationship should hold between tl and all
       the elements reachable from tl, represented in the above by tl->tl.
    *)
    let mu_mapping = parallel_type_walk (P.deref @@ P.template) target_path cont_ty (fun k (in_ap,out_ap) () ->
        match k with
        | `Mu -> `K (fun _ acc ->
                     (in_ap, root_template_at template out_ap)::acc
                   )
        | _ -> `Cont ()
      ) (fun _ _ _ acc -> acc) () []
    in

    (* now we compute the R(hd, tl) /\ R(hd, tl->tl) component. We use the multi_subst operation for this *)
    let unfolding_mu = List.fold_left (fun acc (src_mu, target_mu) ->
        let l = target_mu.hd :: (P.PathMap.bindings target_mu.recurse |> List.map snd) in
        P.PathMap.add src_mu l acc
      ) P.PathMap.empty mu_mapping
    in

    let rec combination_loop l =
      match l with
      | [] -> [P.PathMap.empty]
      | (src_mu,possibilities)::t ->
        let comb = combination_loop t in
        ListMonad.bind (fun mu ->
          List.map (fun m ->
            P.PathMap.add src_mu mu m
          ) comb
        ) possibilities
    in
    let combinatorial_subst =
      P.PathMap.bindings unfolding_mu
      |> combination_loop
      |> List.map (fun m ->
          compute_mu_subst source_mu ~hd:source_mu.hd ~tl:m
        )
    in

    let recursive_substs = List.map (fun (in_ap, out_mu) ->
        let rel = P.PathMap.find (P.root_at ~child:in_ap ~parent:source_path) ctxt.recursive_rel in
        (rel, compute_mu_template_subst out_mu)
      ) mu_mapping
    in
    
    let output_flows = partial_subst (P.deref source_path) target_path cont_ty |> List.map (fun (s,d) ->
          (normalize_ap d, Ap s)
        )
    in

    (* now compute the havocs (if requested) *)
    let all_havocs =
      if with_havoc then
        parallel_type_walk (P.deref @@ source_path) target_path cont_ty (fun k (in_ap,out_ap) (ih,oh,parent_mu) ->
          match k with
          | `Summ -> failwith "Impossible?"
          | `Mu -> `ContPath (P.template,P.template,(ih,oh,Some (in_ap,out_ap)))
          | `Ref | `Array ->
            let concr_path = Option.fold ~none:in_ap ~some:(fun (src,_) ->
                P.root_at ~child:in_ap ~parent:src
              ) parent_mu
            in
            let (ih,oh) = OI.SplitMap.find (OI.SBind e_id,concr_path) ctxt.o_hints.OI.splits in
            `Cont (ih = 0.0, oh = 0.0, parent_mu)
        ) (fun (ih,oh,parent_mu) in_ap out_ap acc ->
          
          match parent_mu with
          | None ->
            (* then we have not reached the mu binder yet, these are all direct copies *)
            H.add_havoc in_ap ih @@ H.add_havoc out_ap oh acc
          | Some (mu_ap,dst_root_ap) ->
            let in_path = P.root_at ~child:in_ap ~parent:mu_ap in
            let out_hd = P.root_at ~child:out_ap ~parent:dst_root_ap in
            let acc =
              H.add_havoc out_hd oh acc
              |> H.add_havoc in_path ih
              |> H.add_mu_havoc ~binder:mu_ap ~ty:ref_ty in_ap ih
            in
            RecRelations.get_mu_binders P.template ref_ty |> List.fold_left (fun acc binder ->
                let binder = normalize_ap @@ P.root_at ~child:binder ~parent:dst_root_ap in
                H.add_mu_havoc ~binder ~ty:ref_ty out_ap oh acc
              ) acc
        ) (false, false, None) H.empty_havoc_state
      else
        H.empty_havoc_state
    in

    let all_havocs = { all_havocs with havoc = normalize_havoc all_havocs.havoc } in
    
    let rec_havocs = H.to_rec_havoc all_havocs in
    let ctxt = List.fold_left (fun ctxt (binder_path,target_mu) ->
        let source_mu = (P.root_at ~child:binder_path ~parent:source_path) in
        let src_rel = P.PathMap.find source_mu ctxt.recursive_rel in
        let ctxt = copy_rel ~by_havoc:rec_havocs ~e_id src_rel ~ty:ref_ty source_mu ctxt in
        let dst_root = fst target_mu.hd in
        RecRelations.get_mu_binders P.template ref_ty |> List.fold_left (fun ctxt binder ->
            let target_mu = P.root_at ~child:binder ~parent:dst_root in
            if PPMap.mem target_mu out_mapping then
              let target_mu = PPMap.find target_mu out_mapping in
              copy_rel ~by_havoc:rec_havocs ~e_id ~ty:ref_ty src_rel target_mu ctxt
            else
              ctxt
          ) ctxt
      ) ctxt mu_mapping
    in
 
    let pre_flows = [
      rel ~ty:ZBool @@ mk_relation (Ap (P.to_null source_path)) "=" (BConst is_nonnull_flag);
      relation_subst in_rel [];
    ] @ List.map (fun (rel, subst) ->
          PRelation (rel, normalize_subst subst, None)
        ) recursive_substs
      @ List.map (fun subst ->
          PRelation (in_rel, normalize_subst subst, None)
        ) combinatorial_subst
    in
    let output_subst = augment_havocs output_flows all_havocs.havoc in
    
    let unfold_impl = (pre_flows @ null_pre out_rel output_subst, PRelation (out_rel, output_subst, None)) in
    { ctxt with impl = unfold_impl::ctxt.impl; havoc_set = P.PathSet.union ctxt.havoc_set all_havocs.havoc }

  type ap_subst = (P.concr_ap * P.concr_ap) list

  type copy_policy =
    | Weak
    | Custom of { rename_src: ap_subst; rename_weak: ap_subst; rename_out: ap_subst }

  let fold_to ~oracle:(dst_oracle,src_oracle) ~e_id ~copy_policy ?rec_ext ?havoc_ext ref_ty src_root target_root in_rel out_rel ctxt =
    let src_ap = P.var src_root in
    let cont_ty = match ref_ty with
      | `Ref (_,t) -> t
      | _ -> assert false
    in
    let mu_template = to_mu_template ref_ty in
    let target_ap = P.var target_root in
    let target_mu = root_template_at mu_template (P.var target_root) in
    let mu_map = parallel_type_walk (P.deref @@ P.template) (P.var src_root) cont_ty (fun k (in_ap, out_ap) () ->
        match k with
        | `Mu -> `K (fun _ acc ->
                     (in_ap, root_template_at mu_template out_ap)::acc
                   )
        | _ -> `Cont ()
      ) (fun () _ _ acc -> acc) () []
    in

    let fold_up_map = List.fold_left (fun acc (out_binder,input_mu) ->
        let l = input_mu.hd :: (P.PathMap.bindings input_mu.recurse |> List.map snd) in
        P.PathMap.add out_binder l acc
      ) P.PathMap.empty mu_map
    in

    let fold_up_subst = compute_mu_multi_subst ~skip_hd_ref:true target_mu ~hd:(src_ap, cont_ty) ~tl:fold_up_map in 
    
    let (rename_src,rename_weak,rename_out) =
      match copy_policy with
      | Weak ->
        let weak = ListMonad.bind (fun (_,mu) ->
            compute_copies (fst mu.hd) (fst mu.hd) (snd mu.hd) |> to_copy_stream |> List.filter_map (fun (a,b,k) ->
                if k = `Direct then
                  None
                else
                  Some (a, to_pass_ap b)
              )
          ) mu_map
              
        in
        ([], weak, weak)
      | Custom { rename_src; rename_weak; rename_out } -> (rename_src, rename_weak, rename_out)
    in

    let handle_term oracle st acc =
      let full_path = RecRelations.MuChain.to_concr st in
      let flg = oracle full_path in
      let acc = H.add_havoc full_path flg acc in
      Option.fold ~none:acc ~some:(fun (p,binder) ->
        H.add_mu_havoc ~binder ~ty:ref_ty p flg acc
      ) @@ RecRelations.MuChain.get_mu_path st
    in
    let hstate =
      walk_type cont_ty RecRelations.MuChain.raw_stepper (handle_term dst_oracle) (P.deref @@ P.var target_root, None) H.empty_havoc_state
      |> walk_type (deep_type_normalization cont_ty) RecRelations.MuChain.raw_stepper (handle_term src_oracle) (src_ap, None)
    in

    let by_havoc = H.to_rec_havoc hstate in
    let ctxt = List.fold_left (fun ctxt (dst_binder,src_folded) ->
        let target_mu = P.root_at ~child:dst_binder ~parent:target_ap in
        let ctxt,rel = RecRelations.recursive_rel_for ~e_id ref_ty target_mu ctxt in
        let with_havoc ante ctxt =
          RecRelations.impl_with_havoc ~ante ~by_havoc target_mu rel ctxt
        in
        let (hd_subst,conj_ind) =
          Option.bind rec_ext (P.PathMap.find_opt dst_binder)
          |> Option.value ~default:([], P.PathMap.empty)
        in
        let ctxt =
          RecRelations.get_mu_binders (fst src_folded.hd) (snd src_folded.hd)
          |> List.fold_left (fun ctxt mu_path ->
              let input_rec = P.PathMap.find mu_path ctxt.recursive_rel in
              let input_rec = PRelation (input_rec, [], None) in
              let ante = input_rec :: (Option.to_list @@ P.PathMap.find_opt mu_path conj_ind) in
              with_havoc ante ctxt
            ) ctxt
        in
        let subst = compute_mu_template_subst src_folded |> List.map (function
            | (src, Ap dst) -> (dst, Ap src)
            | _ -> assert false
            ) in
         with_havoc [ PRelation (in_rel, subst @ hd_subst, None) ] ctxt
      ) ctxt mu_map
    in
    let ctxt = List.fold_left (fun ctxt (_, src_folded) ->
        RecRelations.get_mu_binders (fst src_folded.hd) (snd src_folded.hd)
        |> List.fold_left (fun ctxt src_mu ->
            let src_rel = P.PathMap.find src_mu ctxt.recursive_rel in
            copy_rel ~by_havoc ~e_id ~ty:ref_ty src_rel src_mu ctxt
          ) ctxt
      ) ctxt mu_map
    in

    let hstate = match havoc_ext with
      | Some f ->
        let havoc,stable = f ~havoc:hstate.havoc ~stable:hstate.stable in
        { hstate with havoc; stable }
      | None -> hstate
    in
    let havoc_set = P.PathSet.union hstate.havoc @@ P.PathSet.diff ctxt.havoc_set hstate.stable in

    let output_flows flow_subst =
      augment_havocs (flow_subst @ List.map lift_copy rename_out) havoc_set
    in
    let ante = [
      PRelation (in_rel, List.map lift_copy rename_weak, None);
      rel ~ty:ZBool @@ mk_relation (Ap (P.to_null @@ P.var target_root)) "=" (BConst is_nonnull_flag);
      PRelation (in_rel, List.map lift_copy rename_src, None)
    ] in
    let fold_impl =
      let flows = output_flows fold_up_subst in
      let null_ante = null_pre out_rel fold_up_subst in
      let conseq = relation_subst out_rel flows in
      (ante @ null_ante, conseq)
    in
    { ctxt with impl = (fold_impl :: ctxt.impl); havoc_set }
end


(* ty is the type of the src variable (including the reference constructor *)
let%lm do_unfold_copy ~with_havoc ?(out_mapping=PPMap.id_map) ~e_id src_var dst_var (ref_ty: fltype) in_rel out_rel ctxt =
  RecursiveRefinements.unfold_to ~e_id ~with_havoc ~out_mapping ref_ty src_var dst_var in_rel out_rel ctxt

(* folded ty is the type under the reference after the fold, i.e., the
   type of in_ap after folding.
   out_ap is under a ref, i.e. the location in memory where we are folding to.
 *)
let%lm do_fold_copy ~e_id in_ap out_ap folded_ty in_rel out_rel ctxt =
  let dst_oracle = havoc_oracle ctxt (OI.MGen e_id) in
  let ctxt,so = split_oracle (OI.SBind e_id) ctxt in
  let src_oracle p =
    let (f1,_) = so p p in
    f1 = `Havoc
  in
  RecursiveRefinements.fold_to ~oracle:(dst_oracle,src_oracle) ~e_id ~copy_policy:RecursiveRefinements.Weak folded_ty in_ap out_ap in_rel out_rel ctxt       

let apply_identity_flow ?pre = add_relation_flow ?pre []

let const_assign lhs const in_rel out_rel =
  let%bind havoc_state = get_havoc_state in
  let flows = P.PathSet.elements havoc_state |>
      List.fold_left (fun acc p ->
        Havoc p::acc
      ) [ Const (lhs,const) ]
  in
  add_relation_flow flows in_rel out_rel

let vderef v = P.deref @@ P.var v

let rec is_pre_path p =
  match P.tail p with
  | None -> false
  | Some `Deref -> true
  | Some `Len
  | Some `Proj _ -> is_pre_path @@ P.parent p
  | Some _ -> false

let bind_arg ~fn ~cid ~e_id (havoc,stable,in_bind,out_bind,pre_bind) actual formal ty =
  let copies =  compute_copies actual formal ty in
  let direct_copies = to_copy_stream copies in
  let%bind split_oracle = split_oracle (SCall e_id) in
  let%bind fun_info = get_function_info fn in

  let hstate = List.fold_left (fun acc (src,dst,k) ->
      let (havoc,dst_havoc) = split_oracle src dst in
      let acc = 
        match k with
        | `Mu (under_mu_path, _, dst_binder, ty) ->
          H.add_mu_havoc ~ty ~binder:dst_binder under_mu_path (dst_havoc = `Havoc) acc
        | _ -> acc
      in
      H.add_havoc src (havoc = `Havoc) acc
    ) H.empty_havoc_state direct_copies
  in
  let id_paths = hstate.H.stable in

  let in_bind = List.fold_left (fun in_bind (src,dst,k) ->
      let in_bind = (dst, Ap src)::in_bind in
      if is_pre_path src && (k = `Direct) then
        (P.pre dst, Ap src)::in_bind
      else
        in_bind
    ) in_bind direct_copies
  in
  
  let%bind havoc_out_oracle = gen_oracle (OI.MOut fn) in

  (* dst is the access path for the argument *)
  let (havoc,stable,out_bind,pre_bind) = List.fold_left (fun (havoc,stable,out_bind,pre_bind) (src,dst,k) ->
      let is_pre = is_pre_path src && k = `Direct in
      let is_id = P.PathSet.mem src id_paths in
      let havoc_out = havoc_out_oracle dst && (not is_id) in
      let (havoc,stable) =
        if havoc_out then
          (P.PathSet.add src havoc),stable
        else
          havoc,(P.PathSet.add src stable)
      in

      let out_copy = (dst,Ap src) in
      let pre_path = P.map_root (fun p -> p ^ "!call") src in
      let pre_copy = (src,Ap pre_path) in

      (* to understand what's happening below, let the input state with a single argument x be IN(x).
         The successour state is SUCC(x) and the output predicate is OUT. OUT may (or may not) have
         a pre argument, with formal names $0 and $0!pre *)

      (* now compute the out flows, let's do the easy case first *)
      if (not is_pre) && is_id then
        (* Then this is an argument that may not change during execution and for which we do not track
           pre-states then no pre-substitutions are necessary *)

        (* Then we want to do the following IN(x) /\ OUT(x) => SUCC(x), i.e. the values are all the same.
           out copy is $0 -> x *)
        (havoc,stable,out_copy::out_bind,pre_bind)
      else if (not is_pre) then
        (* this argument may change during execution, and we do not track pre-states. Then create a fresh
           name for the input value (using pre) *)

        (* Then we have IN(x') /\ OUT(x) => SUCC(x). Pre_copy here renames x in IN to x'
           and out_copy is $0 -> x' *)
        (havoc,stable,out_copy::out_bind,pre_copy::pre_bind)
      else if is_pre && is_id then
        (* we track pre states but the argument won't change during execution.
           So constrain the pre-value to be equal to the output argument (do not rename pre) *)

        (* Then we have IN(x) /\ OUT(x,x) => SUCC(x) out_copy is as above, and the second substitution gives $0!pre -> x *)
        (havoc,stable,(P.pre dst,Ap src)::out_copy::out_bind,pre_bind)
      else
        (* finally, we track pre states, and the value may change.
           rename the name in the prestate to be pre,
           and rename the pre path in the output *)

        (* Then we have IN(x') /\ OUT(x, x') => SUCC(x)

           Our out substitutions are $0!pre -> x' and $0 -> x, and our precopy renames x in IN to x' *)
        (havoc,stable,(P.pre dst,Ap pre_path)::out_copy::out_bind,pre_copy::pre_bind)
    ) (havoc,stable,out_bind,pre_bind) direct_copies
  in
  let mu_copy = to_mu_copies copies in
  let%lm update_in_rel susp (_,src_mu, dst_mu, _) ctxt =
    let ctxt,() = susp ctxt in
    let in_rel = P.PathMap.find src_mu ctxt.recursive_rel in
    let out_rel = P.PathMap.find dst_mu fun_info.in_recursive_rel in
    RecRelations.impl_with_havoc ~out_shift:cid ~by_havoc:hstate.mu_havoc ~ante:[
      PRelation (in_rel, [], None)
    ] dst_mu out_rel ctxt
  in
  let%bind () = List.fold_left update_in_rel (return ()) mu_copy in
  let%lm update_out_rel susp (_, src_mu, dst_mu, ty) ctxt =
    let ctxt,() = susp ctxt in
    let out_rel = P.PathMap.find dst_mu fun_info.out_recursive_rel in
    let ctxt,result_rel = RecRelations.recursive_rel_for ~e_id ty src_mu ctxt in
    { ctxt with impl = ([ PRelation (out_rel, [], Some cid) ], PRelation (result_rel, [], None))::ctxt.impl }
  in
  let%bind () = List.fold_left update_out_rel (return ()) mu_copy in
  return (havoc,stable,in_bind,out_bind, pre_bind)

let bind_return ~fn ~e_id ~cid out_patt ret_type =
  let copies =  compute_patt_copies P.ret out_patt ret_type in
  let direct_copies = to_copy_stream copies in
  let%bind havoc_oracle = gen_oracle @@ MRet fn in
  let havoc_ret = List.fold_left (fun acc (src,dst,_) ->
      if havoc_oracle src then
        P.PathSet.add dst acc
      else
        acc
    ) P.PathSet.empty direct_copies in
  let%bind fun_info = get_function_info fn in
  let%bind () =
    List.fold_left (fun m_unit (_,src_mu,dst_mu,ty) ->
      (fun ctxt ->
        let ctxt,() = m_unit ctxt in
        let ctxt,rel = RecRelations.recursive_rel_for ~e_id ty dst_mu ctxt in
        let return_rel = P.PathMap.find src_mu fun_info.out_recursive_rel in
        { ctxt with impl = ([ PRelation(return_rel, [], Some cid) ], PRelation(rel, [], None))::ctxt.impl },()
      )
    ) (return ()) (to_mu_copies copies)
  in
  return (List.map (fun (s,d,_) -> (s,Ap d)) direct_copies,havoc_ret)

let bind_args ~e_id out_patt call_expr curr_rel body_rel =
  let callee = call_expr.callee in
  let%bind callee_type = get_function_type callee in
  let%bind in_rel = get_in_relation callee in
  let%bind out_rel = get_out_relation callee in
  let args = call_expr.arg_names in
  let%bind (havoc,stable,in_bindings,out_bindings,pre_bindings) = fold_left2i (fun i acc arg_name arg_ty ->
      let%bind acc = acc in
      bind_arg ~fn:callee ~cid:call_expr.label ~e_id acc (P.var arg_name) (P.arg i) arg_ty
    ) (return (P.PathSet.empty,P.PathSet.empty,[],[],[])) args callee_type.arg_types
  in
  let%bind (return_bindings,havoc_bind) = bind_return ~fn:callee ~e_id ~cid:call_expr.label out_patt callee_type.ret_type in
  let%bind havoc_state = get_havoc_state in
  let havoc_state = P.PathSet.union havoc_bind @@ P.PathSet.union (P.PathSet.diff havoc_state stable) havoc in

  let havoc_subst =
    P.PathSet.elements havoc_state |> List.mapi (fun i p ->
        (p,Ap (havoc_ap i p))
      )
  in
  begin%m
      add_implication [
      PRelation (curr_rel,[],None)
    ] @@ PRelation (in_rel,in_bindings, Some call_expr.label);
       add_implication [
         PRelation (curr_rel,pre_bindings,None);
         PRelation (out_rel,return_bindings @ out_bindings,Some call_expr.label)
       ] @@ PRelation (body_rel,havoc_subst,None);
       set_havoc_state havoc_state
  end

let process_intrinsic out_patt call_expr intr_type curr_rel body_rel =
  (* check pre-conditions *)
  (* TODO: factor this out *)
  let arg_names = fold_lefti (fun i acc arg ->
      StringMap.add (P.arg_name i) arg acc
    ) StringMap.empty call_expr.arg_names
  in
  let type_fail () = failwith @@ "Cannot handle non-integer typed args in built in functions: " ^ call_expr.callee in
  let%bind () =
    miteri (fun i t ->
      let nu_arg = P.var (List.nth call_expr.arg_names i) in
      match t with
      | RT.Int r ->
        lift_refinement ~map:(P.map_root (fun n -> SM.find n arg_names)) ~nu_arg r
        |> miter @@ add_implication [ PRelation (curr_rel,[],None) ]
      | _ -> type_fail ()
    ) intr_type.RT.arg_types
  in
  match out_patt with
  | PNone -> return ()
  | PVar v -> 
    let pre =
      match intr_type.RT.result_type with
      | Int r -> lift_refinement ~map:(P.map_root (fun n -> SM.find n arg_names)) ~nu_arg:(P.var v) r
      | _ -> type_fail ()
    in
    apply_identity_flow ~pre curr_rel body_rel
  | PTuple _ -> type_fail ()


let process_call ~e_id out_patt call_expr curr_rel body_rel =
  let%bind st = copy_state in
  if StringMap.mem call_expr.callee st.bif_types then
    process_intrinsic out_patt call_expr (StringMap.find call_expr.callee st.bif_types) curr_rel body_rel
  else
    bind_args ~e_id out_patt call_expr curr_rel body_rel

let add_indexing_assertion arr_ap ind_ap relation =
  let array_len = P.len arr_ap in
  let%bind () = add_implication [ PRelation(relation,[],None) ] @@ NamedRel ("valid-ind",[Ap ind_ap; Ap array_len ]) in
  add_implication [ PRelation(relation,[],None) ] @@ rel ~ty:ZInt (mk_relation (Ap array_len) ">" (IConst 0))
  
let nonnull_flow p = NullConst (P.to_null p, is_nonnull_flag)

let apply_patt ~e_id tyenv patt rhs =
  match patt,rhs with
  | _,Call c -> process_call ~e_id patt c
  | PNone,_ -> apply_identity_flow ?pre:None
  | _,Var s ->
    let path = P.var s in
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) @@ compute_patt_copies path patt @@ path_simple_type tyenv path
  | PVar s,Const n -> add_relation_flow [ Const (P.var s,n) ]
  | PVar s,Mkref RNone ->
    add_relation_flow [ Havoc (vderef s); (nonnull_flow @@ P.var s)  ]
  | PVar s,Mkref (RInt n)  ->
    add_relation_flow [ Const (vderef s,n); (nonnull_flow @@ P.var s) ]
  | PVar s,Mkref (RVar v) ->
    apply_copies ~flows:[ (nonnull_flow @@ P.var s) ] ~havoc:false ~sl:(OI.SBind e_id) @@ compute_copies (P.var v) (vderef s) @@ path_simple_type tyenv (P.var v)

  | _,Deref v ->
    let copies = compute_patt_copies (vderef v) patt @@ path_simple_type tyenv (vderef v) in
    apply_copies ~pre:[ rel ~ty:ZBool @@ mk_relation (Ap (P.to_null @@ P.var v)) "=" (BConst is_nonnull_flag) ] ~havoc:false ~sl:(OI.SBind e_id) copies

  | PVar t,Tuple tl ->
    let tup_root = P.var t in
    let flows,copies = fold_lefti (fun i (flows,copies) r ->
        let tgt_ap = P.t_ind tup_root i in
        match r with
        | RNone -> (Havoc tgt_ap)::flows,copies
        | RInt n -> Const (tgt_ap,n)::flows,copies
        | RVar v ->
          let src_type = path_simple_type tyenv @@ P.var v in
          flows,ccat (compute_copies (P.var v) tgt_ap src_type) copies
      ) ([],empty_copy) tl
    in
    apply_copies ~havoc:false ~sl:(OI.SBind e_id) ~flows copies

  | PTuple _,Tuple _ -> assert false
  | PTuple _,_ -> assert false
  | PVar v,Nondet None -> add_relation_flow [ Havoc (P.var v) ]
  | PVar v,Nondet (Some r) ->
    let refinement = lift_refinement ~nu_arg:(P.var v) r in
    apply_identity_flow ~pre:refinement
    
  | PVar v,MkArray len_var ->
    (fun in_rel out_rel ->
      let%bind () = add_assert (Ap (P.var len_var)) ">=" (IConst 0) in_rel in
      let array_root = (P.var v) in
      let l = P.var len_var in
      let ind = P.ind array_root in
      let elem = P.elem array_root in
      let valid_sym_ind = [
        NamedRel ("valid-ind", [Ap ind; Ap l ])
      ] in
      add_relation_flow ~pre:valid_sym_ind [ Const (elem, 0); Copy (l,P.len array_root) ] in_rel out_rel)
  | PVar v,LengthOf arr ->
    add_relation_flow ?pre:None [ Copy (P.len (P.var arr), P.var v) ]
  | PVar v,Read (arr,ind) ->
    (fun in_rel out_rel ->
      let arr_ap = P.var arr in
      let ind_ap = P.var ind in
      
      let array_ind = P.ind arr_ap in
      let elem_ap = P.elem arr_ap in
      let%bind () = add_indexing_assertion arr_ap ind_ap in_rel in
      let copy_pre_cond = PRelation (in_rel,[
            (array_ind, Ap ind_ap);
            (elem_ap, Ap (P.var v))
          ], None) in
      let identity_cond = PRelation (in_rel, [], None) in
      add_implication [ copy_pre_cond; identity_cond ] @@ PRelation (out_rel,[],None))
  | PVar v,Null ->
    (fun in_rel out_rel ->
      let%bind null_types = get_bound_type e_id in
      let paths = type_to_paths (P.var v) null_types in
      let flows = List.map (fun p ->
          if P.is_nullity p then
            NullConst (p, is_null_flag)
          else
            Havoc p
        ) paths in
      RecRelations.null_for_var ~e_id ~ty:null_types v >>
      H.update_null_havoc ~e_id ~ty:null_types v >>
      add_relation_flow ?pre:None flows in_rel out_rel)

let relation_name ((e_id,_),expr) ctxt =
  let prefix = Printf.sprintf "%s-%d-" (Option.value ~default:"main-fn" ctxt.curr_fun) e_id in
  let kind =
    match expr with
    | Let _ -> "let"
    | Seq _ -> "seq"
    | Assign _ -> "assign"
    | Update _ -> "update"
    | Assert _ -> "assert"
    | Alias _ -> "alias"
    | NCond _ -> "ifnull"
    | Cond _ -> "ifz"
    | EVar _ -> "var"
  in
  prefix ^ kind

let fresh_relation_for curr_relation (((e_id,_),_) as k) ctxt =
  let rel = relation_name k ctxt in
  let (_,args,_) = curr_relation in
  let to_ret = (rel,args, Expr e_id) in
  { ctxt with relations = to_ret::ctxt.relations },to_ret

let fresh_alias_relation ~e_id ~name ~args ctxt =
  let to_ret = name, args, AliasUnfold e_id in
  { ctxt with relations = to_ret::ctxt.relations },to_ret

let to_cont k = (Some k),None

let fresh_bind_relation e_id (relation,tyenv) patt k ctxt =
  let (_,curr_args,_) = relation in
  let bound_type = IntMap.find e_id ctxt.let_types in
  let rec destruct_loop (tyenv,args,rec_paths) patt ty =
    match patt,ty with
    | PVar v,ty ->
      let ty = ty in
      let ty_env = (v,ty)::tyenv in
      let paths = List.rev @@ type_to_paths (P.var v) ty in
      let rec_paths = (RecRelations.get_mu_binders (P.var v) ty) @ rec_paths in
      let args = (List.map (fun p -> (p,path_type p)) paths) @ args in
      (ty_env,args,rec_paths)
    | PTuple pl,`Tuple tl ->
      List.fold_left2 destruct_loop (tyenv,args,rec_paths) pl tl
    | PTuple _,_ -> assert false
    | PNone,_ -> (tyenv,args,rec_paths)
  in
  let (tyenv',args,mu_paths) = destruct_loop (tyenv,[],[]) patt bound_type in
  let bound_paths = List.map (fun (p,_) -> p) args |> P.PathSet.of_list in
  let new_args = curr_args @ (List.rev args) in
  let name = relation_name k ctxt in
  let relation = (name, new_args, Expr e_id) in
  { ctxt with relations = relation::ctxt.relations },(relation,tyenv',(bound_paths,mu_paths))

let%lq get_iso_at e_id ctxt =
  let fold = IntSet.mem e_id ctxt.fold_iso in
  let unfold = IntSet.mem e_id ctxt.unfold_iso in
  assert ((fold <> unfold) || (not fold));
  if fold then
    `IsoFold
  else if unfold then
    `IsoUnfold
  else
    `None

let rec process_expr (((relation : relation),tyenv) as st) continuation ((e_id,_),e) =
  let scoped_effect ~b1 ~b2 ctxt =
    let orig_recursive_rel = ctxt.recursive_rel in
    let orig_havoc_set = ctxt.havoc_set in
    let ctxt1,r1 = b1 ctxt in
    let roll_back = { ctxt1 with havoc_set = orig_havoc_set; recursive_rel = orig_recursive_rel } in
    let ctxt2,r2 = b2 roll_back in
    let () = assert (r1 = r2) in
    let recursive_rel =
      P.PathMap.merge (fun path b1 b2 ->
        match b1,b2 with
        | Some b1, Some b2 ->
          if b1 = b2 then Some (`Keep b1)
          else
            Some (`Merge (b1, b2))
        | None, None -> None
        | _,_ -> failwith @@ Printf.sprintf !"Unbalanced rec maps %{P}" path
      ) ctxt1.recursive_rel ctxt2.recursive_rel in
    let ctxt,recursive_rel = P.PathMap.fold (fun path bind (ctxt,new_map) ->
        match bind with
        | `Keep b -> (ctxt, P.PathMap.add path b new_map)
        | `Merge (b1, b2) ->
          let (_,args,_) = b1 in
          let name = Printf.sprintf !"join-%d-%{P}-%s" e_id path "mu" in
          let rel = (name, args, ExprMu (e_id,path,`Join)) in
          let ctxt = {
            ctxt with
            impl = [
              ([PRelation (b1, [], None)], PRelation(rel, [], None));
              ([PRelation (b2, [], None)], PRelation(rel, [], None))
            ] @ ctxt.impl;
            relations = rel::ctxt.relations
          }
          in
          ctxt, P.PathMap.add path rel new_map
      ) recursive_rel (ctxt2, P.PathMap.empty)
    in
    { ctxt with recursive_rel; havoc_set = P.PathSet.union ctxt1.havoc_set ctxt2.havoc_set },r1
  in
  let post_bind (paths,mu_binders) f ctxt =
    let pset = P.PathSet.of_list mu_binders in
    let ctxt,r = f ctxt in
    { ctxt with
      havoc_set = P.PathSet.diff ctxt.havoc_set paths;
      recursive_rel = P.PathMap.filter (fun p _ ->
          not @@ P.PathSet.mem p pset
        ) ctxt.recursive_rel
    },r
  in
  let%lm save_snapshot ctxt =
    { ctxt with snapshots = IntMap.add e_id {
          gamma = tyenv;
          relation;
          mu_relations = ctxt.recursive_rel
        } ctxt.snapshots
    }
  in
  let%bind iso = get_iso_at e_id in
  save_snapshot >>
  match e with
  | EVar v ->
    begin
      match continuation with
      | (Some out_relation),None ->
        (* intra procedural successor *)
        apply_identity_flow relation out_relation
          
      (* should only happen at the main function *)
      | None,None ->
        return ()

      (* tail position *)
      | (Some out_relation),Some (ret_var,out_rec_rel) ->
        let copies = compute_copies (P.var v) ret_var @@ path_simple_type tyenv (P.var v) in
        apply_copies ~out_rec_rel ~havoc:false ~sl:(SRet e_id) copies relation out_relation
      | None, Some _ -> assert false
    end
    
  | Seq (e1, e2) ->
    let%bind e2_rel = fresh_relation_for relation e2 in
    let%bind () = process_expr st (to_cont e2_rel) e1 in
    process_expr (e2_rel,tyenv) continuation e2
      
  | Assign (lhs,IInt i,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    const_assign (P.deref @@ P.var lhs) i relation k_rel >> process_expr (k_rel,tyenv) continuation k

  | Assign (lhs, IVar rhs,k) when iso = `IsoFold ->
    let%bind k_rel = fresh_relation_for relation k in
    let out_ap = P.var lhs in
    let ty = path_simple_type tyenv out_ap in
    do_fold_copy ~e_id rhs lhs ty relation k_rel >>
    process_expr (k_rel,tyenv) continuation k

  | Assign (lhs,IVar rhs,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    let copies = compute_copies (P.var rhs) (vderef lhs) @@ List.assoc rhs tyenv in
    apply_copies ~havoc:true ~sl:(SBind e_id) copies relation k_rel >>
    process_expr (k_rel,tyenv) continuation k
      
  | Update (arr,ind,rhs,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    let array_ap = P.var arr in
    let ind_ap = P.var ind in
    let rhs_ap = P.var rhs in

    let sym_ind = P.ind array_ap in
    let sym_elem = P.elem array_ap in
    begin%m
        add_indexing_assertion array_ap ind_ap relation;

         add_implication [
           PRelation (relation,[],None)
         ] @@ PRelation (k_rel,[ (sym_elem, Ap rhs_ap); (sym_ind, Ap ind_ap) ], None);
         add_implication [
           PRelation (relation,[],None);
           rel ~ty:ZInt @@ mk_relation (Ap sym_ind) "!=" (Ap ind_ap)
         ] @@ PRelation (k_rel,[], None);
         process_expr (k_rel,tyenv) continuation k
    end
  | Cond (v,e1,e2) ->
    let%bind e1_rel = fresh_relation_for relation e1 in
    let%bind e2_rel = fresh_relation_for relation e2 in
    
    let mk_pre rel_cond = Relation (RT.({
        rel_op1 = Ap (P.var v); rel_cond; rel_op2 = IConst 0 
        }), ZInt)
    in
    begin%m
        apply_identity_flow ~pre:[ mk_pre "=" ] relation e1_rel;
         apply_identity_flow ~pre:[ mk_pre "!=" ] relation e2_rel;
         scoped_effect
           ~b1:(process_expr (e1_rel,tyenv) continuation e1)
           ~b2:(process_expr (e2_rel,tyenv) continuation e2)
    end
  | NCond (v,e1,e2) ->
    let%bind e1_rel = fresh_relation_for relation e1 in
    let%bind e2_rel = fresh_relation_for relation e2 in
    let mk_pre null =
      let null_ap = Ap (P.to_null @@ P.var v) in
      Relation (RT.({
          rel_op1 = null_ap; rel_cond = "="; rel_op2 = BConst null
        }), ZBool);
    in
    let var_type = path_simple_type tyenv @@ P.var v in
    begin%m
        apply_identity_flow ~pre:[ mk_pre is_null_flag ] relation e1_rel;
         apply_identity_flow ~pre:[ mk_pre is_nonnull_flag ] relation e2_rel;
         scoped_effect ~b1:(
           RecRelations.null_for_var ~e_id ~ty:var_type v >>
           H.update_null_havoc ~e_id ~ty:var_type v >>
           process_expr (e1_rel,tyenv) continuation e1
         ) ~b2:(process_expr (e2_rel,tyenv) continuation e2)
    end

  | Let (PVar lhs, Mkref (RVar rhs), k) when iso = `IsoFold ->
    let%bind k_rel,tyenv',bind_info = fresh_bind_relation e_id st (PVar lhs) k in
    let%bind bound_ty = get_bound_type e_id in
    do_fold_copy ~e_id rhs lhs bound_ty relation k_rel >>
    post_bind bind_info @@ process_expr (k_rel,tyenv') continuation k

  | Let (p, Deref rhs, k) when iso = `IsoUnfold ->
    let ref_ty = path_simple_type tyenv @@ P.var rhs in
    let%bind k_rel,tyenv',bind_info = fresh_bind_relation e_id st p k in
    let%bind unfolded_type = get_bound_type e_id in
    let copies = compute_patt_copies (P.var "$uf") p unfolded_type in
    let out_mapping = List.fold_left (fun acc (uf,real_path,_) ->
        PPMap.add uf real_path acc
      ) PPMap.empty @@ to_copy_stream copies in
    let out_mapping = List.fold_left (fun acc (_,uf,real_path,_) ->
        PPMap.add uf real_path acc
      ) out_mapping @@ to_mu_copies copies in
    do_unfold_copy ~with_havoc:true ~e_id ~out_mapping rhs "$uf" ref_ty relation k_rel >>
    post_bind bind_info @@ process_expr (k_rel,tyenv') continuation k

  | Let (patt,rhs,k) ->
    let%bind k_rel,tyenv',bind_info = fresh_bind_relation e_id st patt k in
    apply_patt ~e_id tyenv patt rhs relation k_rel >>
    post_bind bind_info @@ process_expr (k_rel,tyenv') continuation k

  | Assert (assrt, k) ->
    let%bind k_rel = fresh_relation_for relation k in
    add_assert_cond assrt relation >>
    apply_identity_flow relation k_rel >>
    process_expr (k_rel,tyenv) continuation k

  | Alias (lhs, APtrProj (r_var,i), k) when iso = `IsoUnfold->
    let%bind k_rel = fresh_relation_for relation k in
    let lhs_type = path_simple_type tyenv @@ P.var lhs in
    let aliased_type = match deep_type_normalization @@ path_simple_type tyenv (P.var r_var) with
      | `Ref (_,t) -> t
      | _ -> assert false
    in
    let temp_args = type_to_paths (P.var "$uf") aliased_type |> List.map (fun p ->
          p, path_type p
        ) in
    let (curr_rel, curr_args,_) = relation in
    let%bind temp_rel = fresh_alias_relation ~e_id ~name:(curr_rel ^ "$alias") ~args:(curr_args @ temp_args) in
    let%bind () = do_unfold_copy ~with_havoc:false ~e_id r_var "$uf" lhs_type relation temp_rel in
    let flow_root = P.t_ind (P.var "$uf") i in
    let folded_target = P.t_ind (P.deref @@ P.var r_var) i in
    let copies = compute_copies (P.var lhs) flow_root lhs_type in
    let copy_stream = to_copy_stream copies in
    let direct_copies,weak_copies = copy_stream |> List.partition (fun (_,_,k) ->
          k = `Direct
        )
    in
    let pass_through_subst = (List.map (fun (s,_,_) ->
        (s, to_pass_ap s)
      ) weak_copies)
    in
    let rename_weak = pass_through_subst @ List.map (fun (s,d,_) ->
          (d, to_pass_ap s)
        ) weak_copies in
    let rename_out = pass_through_subst @ List.map (fun (s,d,_) -> (s,d)) direct_copies in
    let rename_src = List.map (fun (s,d,_) ->
        (s,d)
      ) copy_stream
    in

    let%lm do_alias_fold ctxt =
      let dst_oracle p =
        if P.has_prefix ~prefix:folded_target p && (p <> (P.to_null folded_target)) then
          havoc_oracle ctxt (OI.MAlias e_id) p
        else
          P.PathSet.mem p ctxt.havoc_set
      in
      let src_oracle _ = true in
      let havoc_oracle = havoc_oracle ctxt (OI.MAlias e_id) in
      let var_havoc = copy_stream |> List.fold_left (fun acc (src,_,k) ->
            let havoc = havoc_oracle src in
            let acc = H.add_havoc src havoc acc in
            match k with
            | `Mu (under_mu_path, binder, _, ty) ->
              H.add_mu_havoc ~binder ~ty under_mu_path havoc acc
            | _ -> acc
          ) H.empty_havoc_state
      in
      let by_havoc = H.to_rec_havoc var_havoc in
      let ante,ctxt = to_mu_copies copies |> List.fold_left (fun (ante,ctxt) (_,src_root,dst_root,ty) ->
            let src_rel = P.PathMap.find src_root ctxt.recursive_rel in
            let ante = P.PathMap.add dst_root (PRelation (src_rel, [], None)) ante in
            let dst_rel = P.PathMap.find dst_root ctxt.recursive_rel in
            let ctxt = RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante:([
                PRelation(src_rel, [], None);
                PRelation(dst_rel, [], None)
              ]) src_root ty ctxt
            in
            ante,ctxt
          ) (P.PathMap.empty, ctxt)
      in
      let hd_subst = parallel_type_walk P.template (P.var lhs) lhs_type (fun _ _ () -> `Cont ()) (fun () i o acc ->
          (o, Ap i)::acc
        ) () []
      in
      
      let havoc_ext ~havoc ~stable =
        (P.PathSet.union havoc var_havoc.havoc, P.PathSet.union stable var_havoc.stable)
      in
      let rec_ext = P.PathMap.singleton (P.t_ind (P.deref P.template) i) (hd_subst, ante) in
      let open RecursiveRefinements in
      let ctxt = fold_to ~oracle:(dst_oracle,src_oracle) ~e_id ~copy_policy:(Custom { rename_src; rename_out; rename_weak}) ~rec_ext ~havoc_ext lhs_type "$uf" r_var temp_rel k_rel ctxt in
      (* now remove all of the $uf stuff *)
      let uf_root = P.var "$uf" in
      let concr_root_p = Fun.negate @@ P.has_prefix ~prefix:uf_root in
      { ctxt with
        havoc_set = P.PathSet.filter concr_root_p ctxt.havoc_set;
        recursive_rel = P.PathMap.filter (fun p _ ->
            concr_root_p p
          ) ctxt.recursive_rel
      }
    in
    do_alias_fold >> process_expr (k_rel,tyenv) continuation k
      
  | Alias (lhs,s_ap,k) ->
    let%bind k_rel = fresh_relation_for relation k in
    let rhs_ap = match s_ap with
      | AVar v -> P.var v
      | AProj (v,i) -> P.t_ind (P.var v) i
      | ADeref v -> P.deref @@ P.var v
      | APtrProj (v,i) -> P.t_ind (P.deref @@ P.var v) i
    in
    let lhs_path = P.var lhs in
    let lhs_type = path_simple_type tyenv lhs_path in
    let rhs_subst = compute_copies lhs_path rhs_ap lhs_type in
    let%bind havoc_oracle = gen_for_alias e_id in
    let direct,left,right,hstate = List.fold_left (fun (direct,left,right,hstate) (src,dst,k) ->
        let hstate =
          if (P.to_null lhs_path) = src then
            hstate
          else
            let s_havoc = havoc_oracle src in
            let d_havoc = havoc_oracle dst in
            let hstate =
              H.add_havoc src s_havoc hstate
              |> H.add_havoc dst d_havoc
            in
            match k with
            | `Mu (under_mu_path, src_root, dst_root, ty) ->
              H.add_mu_havoc ~binder:src_root ~ty under_mu_path s_havoc hstate
              |> H.add_mu_havoc ~binder:dst_root ~ty under_mu_path d_havoc
            | _ -> hstate
        in
        match k with
        | `Direct ->
          (src,dst)::direct,left,right,hstate
        | `Mu _ ->
          direct,(src,dst)::left,(dst,src)::right,hstate
      ) ([],[],[],H.empty_havoc_state) @@ to_copy_stream rhs_subst in
    let direct = List.map lift_copy direct in
    let ante =
      if left <> [] then
        let () = assert (right <> []) in
        [
          PRelation (relation, direct @ List.map lift_copy right, None);
          PRelation (relation, direct @ List.map lift_copy left, None)
        ]
      else
        [ PRelation (relation, direct, None) ]
    in
    let%bind havoc_set = get_havoc_state in
    let havoc_set = P.PathSet.union hstate.havoc @@ P.PathSet.diff havoc_set hstate.stable in
    let out_subst = augment_havocs direct havoc_set in
    let%lm alias_recursive ctxt =
      let by_havoc = H.to_rec_havoc hstate in
      to_mu_copies rhs_subst |> List.fold_left (fun ctxt (_,src,dst,ty) ->
          let src_rel = P.PathMap.find src ctxt.recursive_rel in
          let dst_rel = P.PathMap.find dst ctxt.recursive_rel in
          let ante = [
            PRelation (src_rel, [], None);
            PRelation (dst_rel, [], None)
          ] in
          RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante src ty ctxt
          |> RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante dst ty
        ) ctxt
    in
    set_havoc_state havoc_set >>
    alias_recursive >>
    add_implication ante @@ PRelation (k_rel,out_subst,None) >>
    process_expr (k_rel,tyenv) continuation k

let analyze_function fn ctxt =
  let { in_rel = (in_nm,in_args, isrc);
        out_rel = (out_nm,out_args, osrc);
        f_type = fn_type;
        in_recursive_rel;
        out_recursive_rel;
      } = StringMap.find fn.name ctxt.fenv in
  let initial_env = List.map2 (fun v ty ->
      (v,ty)
    ) fn.args fn_type.arg_types in
  let arg_mapping = fold_lefti (fun i acc nm ->
      StringMap.add (P.arg_name i) nm acc
    ) StringMap.empty fn.args in
  let map_args = List.map (fun (p,ty) ->
      let p' = Paths.map_root (fun t ->
          StringMap.find t arg_mapping
        ) p
      in
      (p',ty)
    )
  in

  let havoc_set = fold_left2i (fun i acc nm ty ->
      List.fold_left (fun acc path ->
        let arg_id = P.map_root (fun _ -> P.arg_name i) path in
        if havoc_oracle ctxt (OI.MArg fn.name) arg_id then
          P.PathSet.add path acc
        else
          acc
      ) acc @@ type_to_paths (P.var nm) ty
    ) P.PathSet.empty fn.args fn_type.arg_types
  in
  let start_rel,direct_out = fold_lefti (fun i acc (arg_name,ty) ->
      let mu_binders = RecRelations.get_mu_binders P.template ty in
      let formal_name = P.arg i in
      List.fold_left (fun (start_rel, out_list) mu_loc ->
        let formal_root = P.root_at ~child:mu_loc ~parent:formal_name in
        let arg_root = P.root_at ~child:mu_loc ~parent:(P.var arg_name) in
        let orel = P.PathMap.find formal_root out_recursive_rel in
        let irel = P.PathMap.find formal_root in_recursive_rel in
        P.PathMap.add arg_root irel start_rel, (arg_root, orel)::out_list
      ) acc mu_binders
    ) (P.PathMap.empty, []) initial_env
  in
  let direct_flow =
    P.PathMap.filter (fun p _ ->
      P.has_prefix ~prefix:P.ret p
    ) out_recursive_rel
  in
  let mapped_in_args = map_args in_args in
  let mapped_out_args = map_args out_args in
  let cont = (Some (out_nm, mapped_out_args,osrc)),Some (P.ret,(direct_flow, direct_out)) in
  let ctxt,() = process_expr ((in_nm,mapped_in_args,isrc),initial_env) cont fn.body {ctxt with curr_fun = Some fn.name; havoc_set; recursive_rel = start_rel } in
  ctxt

let analyze_main start_rel main ctxt =
  let ctxt,() = process_expr (start_rel,[]) (None,None) main ctxt in
  ctxt

let infer ~bif_types (simple_theta,side_results) o_hints (fns,main) =
  let lift_and_unfold = (fun p -> deep_type_normalization @@ simple_to_fltype p) in
  let simple_theta = StringMap.map (fun ft ->
      {
        arg_types = List.map lift_and_unfold ft.arg_types;
        ret_type = lift_and_unfold ft.ret_type
      }
    ) simple_theta in
  let (fenv,relations) = StringMap.fold (fun name ty (theta,rel) ->
      let arg_paths =
        List.mapi (fun i arg_t ->
          type_to_paths ~pre:true (P.arg i) arg_t
        ) ty.arg_types
      in
      let in_rel_types = List.map (fun p -> (p,path_type p)) @@ List.concat arg_paths in
      let ret_rel = type_to_paths P.ret ty.ret_type |> List.map (fun p -> (p,path_type p)) in
      let out_rel_types = in_rel_types @ ret_rel in
      let in_rel = (name ^ "-in", in_rel_types, Fun (name, `In)) in
      let out_rel = (name ^ "-out", out_rel_types, Fun (name, `Out)) in
      let in_rec_rel,out_rec_rel,rel = fold_lefti (fun i acc arg_t ->
          RecRelations.get_recursive_roots (P.arg i) arg_t
          |> List.fold_left (fun acc (root,ty) ->
              let args = type_to_paths P.template ty |> List.map (fun p -> p, path_type p) in
              RecRelations.get_mu_binders root ty |> List.fold_left (fun (in_rec_rel, out_rec_rel, rel) mu_binder ->
                  let f suff mu = Printf.sprintf !"%s-%s-%{P}-%s" name suff mu "mu" in
                  let in_name = f "in" mu_binder in
                  let out_name = f "out" mu_binder in
                  let in_rel = (in_name, args, FunMu (name, `In, mu_binder)) in
                  let out_rel = (out_name, args, FunMu (name, `Out, mu_binder)) in
                  (RecRelations.update_rel_map mu_binder in_rel in_rec_rel,
                   RecRelations.update_rel_map mu_binder out_rel out_rec_rel,in_rel::out_rel::rel)
                ) acc
            ) acc
        ) (P.PathMap.empty, P.PathMap.empty, rel) ty.arg_types
      in
      let out_rec_rel,rel =
        RecRelations.get_recursive_roots P.ret ty.ret_type
        |> List.fold_left (fun acc (root,ty) ->
            let args = type_to_paths P.template ty |> List.map (fun p -> p, path_type p) in
            RecRelations.get_mu_binders root ty
            |> List.fold_left (fun (out_rec_rel,rel) root ->
                let nm = Printf.sprintf !"%s-out-%{P}-%s" name root "mu" in
                let ret_rel = (nm, args, FunMu (name,`Out,root)) in
                RecRelations.update_rel_map root ret_rel out_rec_rel, ret_rel::rel
              ) acc
          ) (out_rec_rel,rel)
      in
      let ftype = {
        in_recursive_rel = in_rec_rel;
        out_recursive_rel = out_rec_rel;
        in_rel;
        out_rel;
        f_type = ty
      } in
      (StringMap.add name ftype theta,in_rel::out_rel::rel)
    ) simple_theta (StringMap.empty, [])
  in
  let start_name = "program-start" in
  let entry_relation = (start_name, [], Start) in
  let relations = entry_relation::relations in
  let empty_ctxt = {
    relations;
    o_hints;
    curr_fun = None;
    let_types = IntMap.map lift_and_unfold (side_results.SimpleChecker.SideAnalysis.let_types);
    bif_types;
    fenv;
    impl = [];
    havoc_set = P.PathSet.empty;
    fold_iso = side_results.SimpleChecker.SideAnalysis.fold_locs;
    unfold_iso = side_results.SimpleChecker.SideAnalysis.unfold_locs;
    recursive_rel = P.PathMap.empty;
    snapshots = IntMap.empty
  } in
  let ctxt = List.fold_left (fun ctxt fn ->
      analyze_function fn ctxt
    ) empty_ctxt fns in
  let ctxt = analyze_main entry_relation main
      { ctxt with
        curr_fun = None; havoc_set = P.PathSet.empty; recursive_rel = P.PathMap.empty
      }
  in
  (ctxt.relations,ctxt.impl,ctxt.snapshots,start_name)

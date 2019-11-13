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

module L = Log.Located(struct let where = "FLOW" end)
open L

type z3_types =
  | ZBool
  | ZInt

type flow =
  | Havoc of P.concr_ap
  | Copy of P.concr_ap * P.concr_ap
  | Const of P.concr_ap * int
  | NullConst of P.concr_ap * bool

type relation = string * (P.concr_ap * z3_types) list

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

type ctxt = {
  relations: relation list;
  impl: (clause list * clause) list;
  o_hints: float OI.ownership_ops;
  fenv: (relation * relation * funtype) SM.t;
  curr_fun : string option;
  let_types: fltype Std.IntMap.t;
  bif_types : RefinementTypes.funtype SM.t;
  havoc_set : P.PathSet.t;
  unfold_iso: Std.IntSet.t;
  fold_iso: Std.IntSet.t;
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
  let (_,_,to_ret) = StringMap.find f_name ctxt.fenv in
  to_ret

let%lq get_in_relation f_name ctxt =
  let (ir,_,_) = StringMap.find f_name ctxt.fenv in
  ir

let%lq get_out_relation f_name ctxt =
  let (_,o_rel,_) = StringMap.find f_name ctxt.fenv in
  o_rel

let%lq copy_state ctxt = ctxt

let%lm set_havoc_state havoc_state ctxt = { ctxt with havoc_set = havoc_state }

let%lq get_havoc_state ctxt = ctxt.havoc_set

let%lq get_bound_type e_id ctxt = Std.IntMap.find e_id ctxt.let_types

let mk_relation lhs op rhs = RT.({
    rel_op1 = lhs;
    rel_cond = op;
    rel_op2 = rhs
  })

let rel ~ty k = Relation (k,ty)

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
  let p = P.to_concrete p in
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
    let (f1,f2) = OI.SplitMap.find (sl,p) ctxt.o_hints.OI.splits in
    (f1 = 0.0, f2 = 0.0)
  in
  let rec loop p1 p2 =
    match (P.tail p1),(P.tail p2) with
    | None,_ -> (false,false)
    | _,None -> (false, false)
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

let null_pre (_,args) subst =
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

let havoc_ap d = P.map_root (to_havoc d)

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
  let add_path pre under_summ under_ref under_mu acc p =
    let paths =
      (if under_summ then [P.summ p] else []) @
        (if under_ref && not under_mu && pre then
           [P.pre p] else []) @
        [p]
    in
    paths @ acc
  in
  let rec loop under_summ under_ref under_mu acc p = function
    | `Int -> add_path pre under_summ under_ref under_mu acc p
    | `Ref (summ,t) ->
      let acc = add_path pre (summ || under_summ) under_ref under_mu acc (P.to_null p) in
      loop (summ || under_summ) true under_mu acc (P.deref p) t
    | `Tuple tl ->
      fold_lefti (fun i acc t ->
          loop under_summ under_ref under_mu acc (P.t_ind p i) t
        ) acc tl
    | `IntArray ->
      List.fold_left (add_path false under_summ under_ref under_mu) acc [(P.len p);(P.ind p);(P.elem p)]
    | `Mu t -> loop false under_ref true acc p t
    | `TVar -> acc
  in
  loop false false false [] root ty

let path_step k p = match k with
  | `Ind -> P.ind p
  | `Length -> P.len p
  | `Elem -> P.elem p
  | `Tuple i -> P.t_ind p i
  | `Mu -> p
  | `Ref -> P.deref p
  | `Null -> P.to_null p
  | _ -> failwith "Unsupported"

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
    let mst = step `Summ st in
    continue ~acc mst (fun st' acc ->
      let mst = step `Null st' in
      continue ~acc mst (fun st'' acc ->
        let acc = f st'' acc in
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
      let acc = walk_type ty step f st' acc in
      let mst = step `Ind st in
      continue ~acc mst (fun st' acc ->
        let acc = walk_type ty step f st' acc in
        let mst = step `Elem st in
        continue ~acc mst (walk_type ty step f)
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
    | `Ind -> user_step P.ind `Arr
    | `Elem -> parallel_step P.elem
    | `Length -> parallel_step P.len
    | `Tuple i -> parallel_step ((Fun.flip P.t_ind) i)
    | `Null -> parallel_step P.to_null
    | `Summ -> user_step Fun.id `Summ
  ) (fun (in_ap, out_ap, st) acc ->
    f st in_ap out_ap acc
  ) (in_ap, out_ap, st) acc

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
    parallel_type_walk s d ty (fun k _ st ->
      match k with
      | `Summ -> `Cont false
      | `Mu -> `Cont true
      | `Ref | `Arr -> `Cont st
    ) (fun mu in_ap out_ap acc ->
      if mu then
        (in_ap, out_ap, `Mu)::acc
      else
        (P.summ in_ap, P.summ out_ap, `Summ (in_ap, out_ap))::(in_ap, out_ap, `Direct)::acc
    ) false acc
  ) l weak_copies

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

let add_havoc p f (havoc,stable) =
  if f then
    P.PathSet.add p havoc, stable
  else
    havoc,P.PathSet.add p stable

let augment_havocs flows havoc_set =
  List.filter (fun (p,_) -> not (P.PathSet.mem p havoc_set)) flows |> P.PathSet.fold (fun p acc ->
      (p, Ap (havoc_ap 0 p))::acc
    ) havoc_set  

let compute_flows ~sl copies ctxt =
  let _,split_oracle = split_oracle sl ctxt in
  to_copy_stream copies |> List.fold_left (fun (hstate,rename_copy,copy_subst,out_subst) (src,dst,k) ->
      let (h_in,h_out) = match k with
        | `Summ (a,b) -> split_oracle a b
        | _ -> split_oracle src dst
      in
      let hstate = add_havoc src h_in @@ add_havoc dst h_out hstate in
      let rename_copy, copy_subst, out_subst = match k with
        | `Direct -> rename_copy,copy_subst,(dst, Ap src)::out_subst
        | `Mu | `Summ _ ->
          (dst, Ap (to_pass_ap src))::rename_copy,(src, Ap dst)::copy_subst, out_subst
      in
      (hstate,rename_copy,copy_subst,out_subst)
    ) ((P.PathSet.empty,P.PathSet.empty),[],[],[])

let%lm apply_copies ~havoc:havoc_flag ~sl ?(flows=[]) ?pre copies in_rel out_rel ctxt =
  let (havoc,stable),rename_copy,copy_flows,out_flows = compute_flows ~sl copies ctxt in
  let havoc_set = ctxt.havoc_set in
  let havoc_set = P.PathSet.union havoc @@ P.PathSet.diff havoc_set stable in
  let applied_havocs = if havoc_flag then havoc_set else havoc in
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
  { ctxt with havoc_set; impl = (pre, conseq)::ctxt.impl }

module type SUJMAP = sig
  type t
  type f_key
  type b_key
  val empty : t
  val add : f_key -> b_key -> t -> t
  val mem : f_key -> t -> bool
  val inv_mem : b_key -> t -> bool
  val find : f_key -> t -> b_key
  val inv_find : b_key -> t -> f_key
  val forward : t -> (f_key * b_key) list
end

module SurjectiveMap(F: Map.OrderedType)(B: Map.OrderedType) : SUJMAP with type f_key = F.t with type b_key = B.t = struct
  module FMap = Map.Make(F)
  module BMap = Map.Make(B)
  type t = (B.t FMap.t * F.t BMap.t)
  type f_key = F.t
  type b_key = B.t

  let empty = (FMap.empty, BMap.empty)
  let add k v (f,b) =
    if BMap.mem v b && (BMap.find v b <> k) then
      raise @@ Invalid_argument "duplicate codom elem"
    else
      (FMap.add k v f,BMap.add v k b)

  let inv_mem k (_,d) = BMap.mem k d
  let mem k (d,_) = FMap.mem k d
  let find k (d,_) = FMap.find k d
  let inv_find k (_,d) = BMap.find k d
  let forward (f,_) = FMap.bindings f
end

module IdSurjMap(F: Map.OrderedType) : sig
  include SUJMAP with type f_key = F.t with type b_key = F.t
  val id_map : t
end = struct
  module W = SurjectiveMap(F)(F)
  type t = W.t option
  type f_key = F.t
  type b_key = F.t
  let empty = Some W.empty
  let id_map = None
  let add k v = function
    | None -> failwith "Cannot add to infinite map"
    | Some w -> Some (W.add k v w)

  let q f = fun k -> Option.fold ~none:true ~some:(f k)

  let mem = q W.mem
  let inv_mem = q W.inv_mem
  let l f = fun k -> Option.fold ~none:k ~some:(f k)

  let find = l W.find
  let inv_find = l W.inv_find

  let forward = function
    | None -> []
    | Some w -> W.forward w
end

module PPMap = IdSurjMap(P.PathOrd)

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
       
  let compute_frag_subst ?(acc=[]) ~is_tail ~skip_ref concr src_frag dst_frag =
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
    let inj = if is_tail then Fun.id else P.summ in
    parallel_type_walk src dst ty (fun k _ () ->
      match k with
      | `Mu -> `K (fun _ acc -> acc)
      | `Summ | `Arr | `Ref -> `Cont ()
    ) (fun () in_ap out_ap acc ->
      let out_ap = if concr then out_ap else P.summ out_ap in
      (inj in_ap, out_ap)::acc
    ) () acc

  let compute_mu_subst ?(skip_hd_ref=false) src_templ ~hd:(hfrag,hconcr) ~tl:(tfrags,tconcr) =
    let subst = compute_frag_subst ~skip_ref:skip_hd_ref ~is_tail:false hconcr src_templ.hd hfrag in
    P.PathMap.fold (fun bind_path src_frag acc ->
      let dst_frag = P.PathMap.find bind_path tfrags in
      compute_frag_subst ~skip_ref:false ~is_tail:true ~acc tconcr src_frag dst_frag
    ) src_templ.recurse subst |> List.map lift_copy

  let compute_mu_multi_subst ?(skip_hd_ref=false) src_templ ~hd:(hfrag,hconcr) ~tl:tfrags =
    let subst = compute_frag_subst ~skip_ref:skip_hd_ref ~is_tail:false hconcr src_templ.hd hfrag in
    let indexed_subst = P.PathMap.fold (fun bind_path src_frag acc ->
      let dst_frags = P.PathMap.find bind_path tfrags in
      let sub_group = fold_lefti (fun i acc (dst_frag,tconcr) ->
        let s = compute_frag_subst ~skip_ref:false ~is_tail:true tconcr src_frag dst_frag in
        (i,s)::acc
        ) [] dst_frags in
      sub_group::acc
      ) src_templ.recurse []
    in
    to_multi_subst subst indexed_subst

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

    (* rougly speaking, we unfold a recursive relation R(x,?,y) as follows:
       R(x,T,hd) /\ R(hd,F,tl) /\ R(x,T,tl) => T(hd,?,tl)

       here, x is the head component y is the tail component. T is the relation describing the
       recursive relationship in the unfolding.

       We label the substitutions below following this intuition
    *)
    let mu_mapping = parallel_type_walk (P.deref @@ P.template) target_path cont_ty (fun k (in_ap,out_ap) () ->
        match k with
        | `Mu -> `K (fun _ acc ->
                     (in_ap, root_template_at template out_ap)::acc
                   )
        | _ -> `Cont ()
      ) (fun _ _ _ acc -> acc) () []
    in
    (* R(hd, F, tl), i.e. assert the output mu conforms to the input mu *)
    let trans_subst = List.map (fun (_,out_mu) ->
        compute_mu_subst source_mu ~hd:(out_mu.hd,false) ~tl:(out_mu.recurse,true)
      ) mu_mapping
    in
    (* R(x,T, hd), i.e., the new heads are generated in relation to the current head *)
    let hd_map = List.fold_left (fun acc (k,v) ->
        P.PathMap.add k v.hd acc
      ) P.PathMap.empty mu_mapping
    in  
    (* And now for the head element *)
    let hd_gen_subst =
      compute_mu_subst source_mu ~hd:(source_mu.hd,true) ~tl:(hd_map,true)
    in

    let outer_subst = compute_mu_subst source_mu ~hd:(source_mu.hd,true) ~tl:(hd_map,false) in

    (* And now the messy bit, R(x, T, tl).

       Given the existence of multiple mu binders, there will be multiple "tail" values
       to be constrained for every (unfolded) head position. So we collapse them all
       below using the to_multi_subst function
    *)
    let outer_trans =
      let multi_bind = List.fold_left (fun acc (mu_path,mu) ->
          let l = (mu.hd,false) :: (P.PathMap.bindings mu.recurse |> List.map (fun (_,m) -> (m,true))) in
          P.PathMap.add mu_path l acc
        ) P.PathMap.empty mu_mapping in
      compute_mu_multi_subst source_mu ~hd:(source_mu.hd, true) ~tl:multi_bind
    in

    let output_flows = partial_subst (P.deref source_path) target_path cont_ty |> List.map (fun (s,d) ->
          (normalize_ap d, Ap s)
        )
    in

    (* now compute the havocs (if requested) *)
    let all_havocs =
      if with_havoc then
        parallel_type_walk (P.deref @@ P.template) P.template cont_ty (fun k (in_ap,out_ap) (ih,oh,parent_mu) ->
          match k with
          | `Summ -> failwith "Impossible?"
          | `Mu -> `ContPath (in_ap,P.template,(ih,oh,Some (in_ap,out_ap)))
          | `Ref | `Arr ->
            let concr_path = P.root_at ~child:in_ap ~parent:source_path in
            let (ih,oh) = OI.SplitMap.find (OI.SBind e_id,concr_path) ctxt.o_hints.OI.splits in
            `Cont (ih = 0.0, oh = 0.0, parent_mu)
        ) (fun (ih,oh,parent_mu) in_ap out_ap acc ->
          let maybe_add ?(summ=false) f p acc =
            if f then
              P.PathSet.add p @@
                if summ then
                  P.PathSet.add (P.summ p) acc
                else
                  acc
            else acc
          in
          match parent_mu with
          | None ->
          (* then we have no reached the mu binder yet, these are all direct copies *)
            let in_ap = P.root_at ~child:in_ap ~parent:source_path in
            let out_ap = P.root_at ~child:out_ap ~parent:target_path in
            maybe_add ~summ:true ih in_ap @@ maybe_add oh out_ap acc
          | Some (_,tgt_ap) ->
            let in_ap = P.root_at ~child:in_ap ~parent:source_path in
            let child_mu = P.root_at ~child:tgt_ap ~parent:target_path in
            let hd_path = P.root_at ~child:out_ap ~parent:child_mu in
            let summ_hd = P.summ hd_path in
            let tl_paths = P.PathMap.bindings template.recurse |> List.map (fun (k,_) ->
                  P.root_at ~child:out_ap ~parent:(P.root_at ~child:k ~parent:child_mu)
                ) in
            let acc = if ih then P.PathSet.add in_ap acc else acc in
            if oh then
              P.PathSet.union acc @@ P.PathSet.of_list ([summ_hd; hd_path]@ tl_paths)
            else
              acc
        ) (false, false, None) P.PathSet.empty |> normalize_havoc
      else
        P.PathSet.empty
    in
 
    let pre_flows = [
      rel ~ty:ZBool @@ mk_relation (Ap (P.to_null source_path)) "=" (BConst is_nonnull_flag);
      relation_subst in_rel @@ normalize_subst outer_trans;
      relation_subst in_rel @@ normalize_subst outer_subst;
      relation_subst in_rel @@ normalize_subst hd_gen_subst;
      relation_subst in_rel [];
    ] @ List.map (relation_subst in_rel) (List.map normalize_subst trans_subst)
    in
    let output_subst = augment_havocs output_flows all_havocs in
    
    let unfold_impl = (pre_flows @ null_pre out_rel output_subst, PRelation (out_rel, output_subst, None)) in
    { ctxt with impl = unfold_impl::ctxt.impl; havoc_set = P.PathSet.union ctxt.havoc_set all_havocs }

  type ap_subst = (P.concr_ap * P.concr_ap) list

  type copy_policy =
    | Weak
    | Custom of { rename_src: ap_subst; rename_weak: ap_subst; rename_out: ap_subst }

  let fold_to ~oracle:(dst_oracle,src_oracle) ~copy_policy ?havoc_ext ref_ty src_root target_root in_rel out_rel ctxt =
    let src_ap = P.var src_root in
    let cont_ty = match ref_ty with
      | `Ref (_,t) -> t
      | _ -> assert false
    in
    let mu_template = to_mu_template ref_ty in
    let target_ap = P.deref @@ P.var target_root in
    let target_mu = root_template_at mu_template (P.var target_root) in
    let mu_map = parallel_type_walk (P.deref @@ P.template) (P.var src_root) cont_ty (fun k (in_ap, out_ap) () ->
        match k with
        | `Mu -> `K (fun _ acc ->
                     (in_ap, root_template_at mu_template out_ap)::acc
                   )
        | _ -> `Cont ()
      ) (fun () _ _ acc -> acc) () []
    in

    let hd_frag = src_ap,cont_ty in
    let fold_up_tl = List.fold_left (fun acc (mu_path,mu) ->
        let l = [mu.hd, true; mu.hd, false] in
        let l = l @ (P.PathMap.bindings mu.recurse |> List.map (fun (_,m) -> (m,true))) in
        P.PathMap.add mu_path l acc
      ) P.PathMap.empty mu_map
    in
    let direct_subst = partial_subst target_ap src_ap cont_ty |> List.map lift_copy in
    let fold_up_subst = ((P.summ @@ P.to_null @@ P.var target_root),BConst is_nonnull_flag) :: compute_mu_multi_subst ~skip_hd_ref:true target_mu ~hd:(hd_frag,true) ~tl:fold_up_tl in
    let fold_up_subst = fold_up_subst @ direct_subst in

    let ind_substs = List.map (fun (_,mu) ->
        direct_subst @ compute_mu_subst target_mu ~hd:(mu.hd,false) ~tl:(mu.recurse, true)
      ) mu_map
    in

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

    let state_stepper = (fun k (st,p) ->
        match k with
        | `Mu -> `Cont (`None, p)
        | `Summ -> `Cont (`Summ, p)
        | _ -> `Cont (st,path_step k p))
    in

    let state_add (st,ap) set =
      let set = P.PathSet.add ap set in
      if st = `Summ then P.PathSet.add (P.summ ap) set else set
    in
    
    let havoc = walk_type (deep_type_normalization cont_ty) state_stepper (fun (st,ap) havoc ->
        if src_oracle ap then
          state_add (st,ap) havoc
        else
          havoc
      ) (`None,src_ap) P.PathSet.empty in
    let havoc,stable = walk_type cont_ty state_stepper (fun (st,ap) (havoc,stable) ->
        if dst_oracle ap then
          state_add (st,ap) havoc,stable
        else
          havoc,state_add (st,ap) stable
      ) (`Summ,target_ap) (havoc,P.PathSet.empty) in

    let havoc,stable = match havoc_ext with
      | Some f -> f ~havoc ~stable
      | None -> havoc,stable
    in
    let havoc_set = P.PathSet.union havoc @@ P.PathSet.diff ctxt.havoc_set stable in

    let output_flows flow_subst =
      augment_havocs (flow_subst @ List.map lift_copy rename_out) havoc_set
    in
    let ante = [
      PRelation (in_rel, List.map lift_copy rename_weak, None);
      rel ~ty:ZBool @@ mk_relation (Ap (P.to_null @@ P.var target_root)) "=" (BConst is_nonnull_flag);
      PRelation (in_rel, List.map lift_copy rename_src, None)
    ] in
    let all_subst = fold_up_subst::ind_substs in
    let to_impl subst = 
      let flows = output_flows subst in
      let null_ante = null_pre out_rel subst in
      let conseq = relation_subst out_rel flows in
      (ante @ null_ante, conseq)
    in
    let fold_impl = List.map to_impl all_subst in
    { ctxt with impl = (fold_impl @ ctxt.impl); havoc_set }
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
    f1
  in
  RecursiveRefinements.fold_to ~oracle:(dst_oracle,src_oracle) ~copy_policy:RecursiveRefinements.Weak folded_ty in_ap out_ap in_rel out_rel ctxt       

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

let bind_arg ~fn ~e_id (havoc,stable,in_bind,out_bind,pre_bind) actual formal ty =
  let direct_copies = compute_copies actual formal ty |> to_copy_stream in
  let%bind split_oracle = split_oracle (SCall e_id) in

  let id_paths = List.fold_left (fun acc (src,dst,k) ->
      let (havoc,_) = match k with
        | `Summ (s,d) -> split_oracle s d
        | `Direct | `Mu -> split_oracle src dst
      in
      if havoc then
        acc
      else
        P.PathSet.add src acc
    ) P.PathSet.empty direct_copies in

  let in_bind = List.fold_left (fun in_bind (src,dst,k) ->
      let in_bind = (dst, Ap src)::in_bind in
      if is_pre_path src && k = `Direct then
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
      let havoc_path = match k with
        | `Summ (_,d) -> d
        | _ -> dst
      in
      let havoc_out = havoc_out_oracle havoc_path && (not is_id) in
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
  return (havoc,stable,in_bind,out_bind, pre_bind)

let bind_return ~fn out_patt ret_type =
  let copies = compute_patt_copies P.ret out_patt ret_type |> to_copy_stream in
  let%bind havoc_oracle = gen_oracle @@ MRet fn in
  let havoc_ret = List.fold_left (fun acc (src,dst,k) ->
      let hsrc = match k with | `Summ (s,_) -> s | `Mu | `Direct -> src in
      if havoc_oracle hsrc then
        P.PathSet.add dst acc
      else
        acc
    ) P.PathSet.empty copies in
  return (List.map (fun (s,d,_) -> (s,Ap d)) copies,havoc_ret)
  
let bind_args ~e_id out_patt call_expr curr_rel body_rel =
  let callee = call_expr.callee in
  let%bind callee_type = get_function_type callee in
  let%bind in_rel = get_in_relation callee in
  let%bind out_rel = get_out_relation callee in
  let args = call_expr.arg_names in
  let%bind (havoc,stable,in_bindings,out_bindings,pre_bindings) = fold_left2i (fun i acc arg_name arg_ty ->
      let%bind acc = acc in
      bind_arg ~fn:callee ~e_id acc (P.var arg_name) (P.arg i) arg_ty
    ) (return (P.PathSet.empty,P.PathSet.empty,[],[],[])) args callee_type.arg_types
  in
  let%bind (return_bindings,havoc_bind) = bind_return ~fn:callee out_patt callee_type.ret_type in
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
    | EAnnot _ -> "$gamma"
  in
  prefix ^ kind

let fresh_relation_for curr_relation k ctxt =
  let rel = relation_name k ctxt in
  let (_,args) = curr_relation in
  let to_ret = (rel,args) in
  { ctxt with relations = to_ret::ctxt.relations },to_ret

let fresh_relation ~name ~args ctxt =
  let to_ret = name, args in
  { ctxt with relations = to_ret::ctxt.relations },to_ret

let to_cont k = (Some k),None

let fresh_bind_relation e_id (relation,tyenv) patt k ctxt =
  let (_,curr_args) = relation in
  let bound_type = Std.IntMap.find e_id ctxt.let_types in
  let rec destruct_loop (tyenv,args) patt ty =
    match patt,ty with
    | PVar v,ty ->
      let ty = ty in
      let ty_env = (v,ty)::tyenv in
      let paths = List.rev @@ type_to_paths (P.var v) ty in
      let args = (List.map (fun p -> (p,path_type p)) paths) @ args in
      (ty_env,args)
    | PTuple pl,`Tuple tl ->
      List.fold_left2 destruct_loop (tyenv,args) pl tl
    | PTuple _,_ -> assert false
    | PNone,_ -> (tyenv,args)
  in
  let (tyenv',args) = destruct_loop (tyenv,[]) patt bound_type in
  let bound_paths = List.map (fun (p,_) -> p) args |> P.PathSet.of_list in
  let new_args = curr_args @ (List.rev args) in
  let name = relation_name k ctxt in
  let relation = (name, new_args) in
  { ctxt with relations = relation::ctxt.relations },(relation,tyenv',bound_paths)

let%lq get_iso_at e_id ctxt =
  let fold = Std.IntSet.mem e_id ctxt.fold_iso in
  let unfold = Std.IntSet.mem e_id ctxt.unfold_iso in
  assert ((fold <> unfold) || (not fold));
  if fold then
    `IsoFold
  else if unfold then
    `IsoUnfold
  else
    `None

let rec process_expr ((relation,tyenv) as st) continuation ((e_id,_),e) =
  let scoped_havoc f ctxt =
    let havoc_set = ctxt.havoc_set in
    let ctxt,r = f ctxt in
    { ctxt with havoc_set },r
  in
  let post_bind paths f ctxt =
    let ctxt,r = f ctxt in
    { ctxt with havoc_set = P.PathSet.diff ctxt.havoc_set paths },r
  in
  let%bind iso = get_iso_at e_id in
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
      | (Some out_relation),Some ret_var ->
        let copies = compute_copies (P.var v) ret_var @@ path_simple_type tyenv (P.var v) in
        apply_copies ~havoc:false ~sl:(SRet e_id) copies relation out_relation
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
         scoped_havoc @@ process_expr (e1_rel,tyenv) continuation e1;
         apply_identity_flow ~pre:[ mk_pre "!=" ] relation e2_rel;
         process_expr (e2_rel,tyenv) continuation e2
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
    begin%m
        apply_identity_flow ~pre:[ mk_pre is_null_flag ] relation e1_rel;
         scoped_havoc @@ process_expr (e1_rel,tyenv) continuation e1;
         apply_identity_flow ~pre:[ mk_pre is_nonnull_flag ] relation e2_rel;
         process_expr (e2_rel,tyenv) continuation e2
    end

  | Let (PVar lhs, Mkref (RVar rhs), k) when iso = `IsoFold ->
    let%bind k_rel,tyenv',bound_set = fresh_bind_relation e_id st (PVar lhs) k in
    let%bind bound_ty = get_bound_type e_id in
    do_fold_copy ~e_id rhs lhs bound_ty relation k_rel >>
    post_bind bound_set @@ process_expr (k_rel,tyenv') continuation k

  | Let (p, Deref rhs, k) when iso = `IsoUnfold ->
    let ref_ty = path_simple_type tyenv @@ P.var rhs in
    let%bind k_rel,tyenv',bound_set = fresh_bind_relation e_id st p k in
    let%bind unfolded_type = get_bound_type e_id in
    let copies = compute_patt_copies (P.var "$uf") p unfolded_type in
    let out_mapping = List.fold_left (fun acc (uf,real_path,_) ->
        PPMap.add uf real_path acc
      ) PPMap.empty @@ to_copy_stream copies in
    do_unfold_copy ~with_havoc:true ~e_id ~out_mapping rhs "$uf" ref_ty relation k_rel >>
    post_bind bound_set @@ process_expr (k_rel,tyenv') continuation k

  | Let (patt,rhs,k) ->
    let%bind k_rel,tyenv',bound_set = fresh_bind_relation e_id st patt k in
    apply_patt ~e_id tyenv patt rhs relation k_rel >>
    post_bind bound_set @@ process_expr (k_rel,tyenv') continuation k
      
  | EAnnot _ -> assert false
    
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
    let (curr_rel, curr_args) = relation in
    let%bind temp_rel = fresh_relation ~name:(curr_rel ^ "$alias") ~args:(curr_args @ temp_args) in
    let%bind () = do_unfold_copy ~with_havoc:false ~e_id r_var "$uf" lhs_type relation temp_rel in
    let flow_root = P.t_ind (P.var "$uf") i in
    let folded_target = P.t_ind (P.deref @@ P.var r_var) i in
    let alias_copies = compute_copies (P.var lhs) flow_root lhs_type |> to_copy_stream in
    let direct_copies,weak_copies = alias_copies |> List.partition (fun (_,_,k) ->
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
      ) alias_copies
    in

    let%lm do_alias_fold ctxt =
      let dst_oracle p =
        let p' = P.to_concrete p in
        if P.has_prefix ~prefix:folded_target p' && (p' <> (P.to_null folded_target)) then
          havoc_oracle ctxt (OI.MAlias e_id) p
        else
          P.PathSet.mem p ctxt.havoc_set
      in
      let src_oracle _ = true in
      let havoc_ext ~havoc ~stable =
        type_to_paths (P.var lhs) lhs_type |> List.fold_left (fun (havoc,stable) p ->
            let p' = P.to_concrete p in
            if havoc_oracle ctxt (OI.MAlias e_id) p' then
              P.PathSet.add p havoc,stable
            else
              havoc,P.PathSet.add p stable
          ) (havoc,stable)
      in
      let open RecursiveRefinements in
      fold_to ~oracle:(dst_oracle,src_oracle) ~copy_policy:(Custom { rename_src; rename_out; rename_weak}) ~havoc_ext lhs_type "$uf" r_var temp_rel k_rel ctxt
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
    let direct,left,right,(havoc,stable) = List.fold_left (fun (direct,left,right,os) (src,dst,k) ->
        let hs,hd =
          match k with
          | `Summ (s,d) -> s,d
          | _ -> src,dst
        in
        let os =
          if (P.to_null lhs_path) = hs then
            os
          else
            let s_havoc = havoc_oracle hs in
            let d_havoc = havoc_oracle hd in
            let os = add_havoc src s_havoc os in
            add_havoc dst d_havoc os
        in
        match k with
        | `Direct ->
          (src,dst)::direct,left,right,os
        | `Summ _
        | `Mu ->
          direct,(src,dst)::left,(dst,src)::right,os
      ) ([],[],[],(P.PathSet.empty, P.PathSet.empty)) @@ to_copy_stream rhs_subst in
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
    let havoc_set = P.PathSet.union havoc @@ P.PathSet.diff havoc_set stable in
    let out_subst = augment_havocs direct havoc_set in
    add_implication ante @@ PRelation (k_rel,out_subst,None) >>
    process_expr (k_rel,tyenv) continuation k

let analyze_function fn ctxt =
  let ((in_nm,in_args),(out_nm,out_args),fn_type) = StringMap.find fn.name ctxt.fenv in
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
    ) P.PathSet.empty fn.args fn_type.arg_types in
  let mapped_in_args = map_args in_args in
  let mapped_out_args = map_args out_args in
  let cont = (Some (out_nm, mapped_out_args)),Some P.ret in
  let ctxt,() = process_expr ((in_nm,mapped_in_args),initial_env) cont fn.body {ctxt with curr_fun = Some fn.name; havoc_set } in
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
      let in_rel = (name ^ "-in", in_rel_types) in
      let out_rel = (name ^ "-out", out_rel_types) in
      let ftype = (in_rel,out_rel,ty) in
      (StringMap.add name ftype theta,in_rel::out_rel::rel)
    ) simple_theta (StringMap.empty, []) in
  let start_name = "program-start" in
  let entry_relation = (start_name, []) in
  let relations = entry_relation::relations in
  let empty_ctxt = {
    relations;
    o_hints;
    curr_fun = None;
    let_types = Std.IntMap.map lift_and_unfold (side_results.SimpleChecker.SideAnalysis.let_types);
    bif_types;
    fenv;
    impl = [];
    havoc_set = P.PathSet.empty;
    fold_iso = side_results.SimpleChecker.SideAnalysis.fold_locs;
    unfold_iso = side_results.SimpleChecker.SideAnalysis.unfold_locs
  } in
  let ctxt = List.fold_left (fun ctxt fn ->
      analyze_function fn ctxt
    ) empty_ctxt fns in
  let ctxt = analyze_main entry_relation main { ctxt with curr_fun = None } in
  (ctxt.relations,ctxt.impl,start_name)

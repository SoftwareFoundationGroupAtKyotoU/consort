open Ast
open Std
open Std.StateMonad
open Sexplib.Std
open OwnershipSolver
    
module SM = StringMap
module SS = StringSet
module P = Paths
    
type 'a otype_ =
  | Array of 'a otype_ * 'a
  | Int
  | Ref of 'a otype_ * 'a
  | Tuple of 'a otype_ list
  | TVar of int
  | Mu of int * 'a otype_

type otype = ownership otype_

type magic_loc =
  | MGen of int
  | MJoin of int
  | MArg of string
  | MOut of string
  | MRet of string
  | MAlias of int [@@deriving sexp]

type split_loc =
  | SBind of int
  | SCall of int
  | SRet of int [@@deriving sexp]

module SplitMap : Map.S with type key = (split_loc * Paths.concr_ap) = Map.Make(OrderedPair(DefaultOrd(struct type t = split_loc end))(P.PathOrd))
module GenMap = Map.Make(OrderedPair(DefaultOrd(struct type t = magic_loc end))(P.PathOrd))

type 'a ownership_ops = {
  splits: ('a * 'a) SplitMap.t;
  gen: 'a GenMap.t
}

type context = {
  ovars: int list;
  v_counter: int;
  iso: SimpleChecker.SideAnalysis.results;
  ocons: ocon list;
  gamma: otype StringMap.t;
  theta: (otype RefinementTypes._funtype) StringMap.t;
  op_record: ownership ownership_ops;
  save_env: otype StringMap.t IntMap.t
}

let unfold =
  let rec subst_once id sub = function
    | TVar id' when id = id' -> sub
    | (Int as t)
    | (TVar _ as t) -> t
    | Ref (t,o) -> Ref (subst_once id sub t,o)
    | Array (t,o) -> Array (subst_once id sub t,o)
    | Tuple tl -> Tuple (List.map (subst_once id sub) tl)
    | Mu (id',t) -> assert (id' <> id); Mu (id',subst_once id sub t)
  in
  let rec unfold_loop ~unfld = function
    | TVar id -> assert (IntSet.mem id unfld); TVar id
    | Int -> Int
    | Ref (t,o) -> Ref (unfold_loop ~unfld t,o)
    | Array (t,o) -> Array (unfold_loop ~unfld t,o)
    | Mu (id,t) when IntSet.mem id unfld ->
      Mu (id,unfold_loop ~unfld t)
    | Tuple tl ->
      Tuple (List.map (unfold_loop ~unfld) tl)
    | (Mu (id,t)) as mu ->
      let t' = subst_once id mu t in
      unfold_loop ~unfld:(IntSet.add id unfld) t'
  in
  unfold_loop ~unfld:IntSet.empty

let%lm add_constraint c ctxt = { ctxt with ocons = c::ctxt.ocons }

let%lm shuffle_types ~e_id ~src:(t1,t1') ~dst:(t2,t2') ctxt =
  let unfold_dst =
    if IntSet.mem e_id ctxt.iso.SimpleChecker.SideAnalysis.unfold_locs then
      unfold
    else Fun.id
  in
  let rec loop t1 t2 t1' t2' ctxt =
    match t1,t2,t1',t2' with
    | Int,Int,Int,Int -> ctxt
    | Array (r1,o1), Array (r2,o2), Ref (r1',o1'), Ref (r2',o2')
    | Ref (r1,o1),Ref (r2,o2), Ref (r1',o1'), Ref(r2',o2') ->
      loop r1 r2 r1' r2' @@
        { ctxt with
          ocons = Shuff ((o1,o2),(o1',o2')) :: ctxt.ocons }
    | Tuple tl1, Tuple tl2, Tuple tl1', Tuple tl2' ->
      let orig_tl = List.combine tl1 tl2 in
      let new_tl = List.combine tl1' tl2' in
      List.fold_left2 (fun ctxt' (te1,te2) (te1',te2') ->
        loop te1 te2 te1' te2' ctxt'
      ) ctxt orig_tl new_tl
    | Mu (_,m1), Mu (_,m2), Mu (_,m1'), Mu (_,m2') ->
      loop m1 m2 m1' m2' ctxt
    | TVar _, TVar _, TVar _, TVar _ -> ctxt
    | _ -> failwith "Type mismatch (simple checker broken D?)"
  in
  loop t1 (unfold_dst t2) t1' (unfold_dst t2') ctxt

let%lm sum_ownership t1 t2 out ctxt =
  let rec loop t1 t2 out ctxt =
    match t1,t2,out with
    | Int, Int, Int -> ctxt
    | Ref (r1,o1), Ref (r2,o2), Ref (ro,oo) ->
      loop r1 r2 ro
        { ctxt with ocons = (Split (oo,(o1,o2)))::ctxt.ocons}
    | Tuple tl1, Tuple tl2, Tuple tl_out ->
      fold_left3i (fun ctxt _ e1 e2 e_out ->
          loop e1 e2 e_out ctxt) ctxt tl1 tl2 tl_out
    | Mu (_,t1'), Mu (_,t2'), Mu (_,out') ->
      loop t1' t2' out' ctxt
    | TVar _,TVar _, TVar _ -> ctxt
    | Array (et1,o1), Array (et2,o2), Array (et3,o3) ->
      loop et1 et2 et3
        { ctxt with ocons = Split (o3,(o1,o2))::ctxt.ocons }
    | _ -> failwith "Mismatched types (simple checker broken C?)"
  in
  loop t1 t2 out ctxt
    
let rec unfold_simple arg mu =
  function
  | `Int -> `Int
  | `Ref t' -> `Ref (unfold_simple arg mu t')
  | `TVar id when id = arg -> mu
  | `TVar id -> `TVar id
  | `Array `Int -> `Array `Int
  | `Tuple tl_list -> `Tuple (List.map (unfold_simple arg mu) tl_list)
  | `Mu (id,t) -> `Mu (id, unfold_simple arg mu t)

let (>>) a b =
  let%bind () = a in
  b

let rec constrain_wf_loop o t ctxt =
  match t with
  | TVar _
  | Int -> (ctxt,())
  | Tuple tl ->
    miter (constrain_wf_loop o) tl ctxt
  | Mu (_,t) -> constrain_wf_loop o t ctxt
  | Ref (t',o')
  | Array (t',o') ->
    constrain_wf_loop o' t' {
        ctxt with ocons = Wf (o,o')::ctxt.ocons
      }

let rec constrain_well_formed = function
  | TVar _
  | Int -> return ()
  | Tuple tl -> miter constrain_well_formed tl
  | Mu (_,t) -> constrain_well_formed t
  | Ref (t,o)
  | Array (t,o) -> constrain_wf_loop o t

let%lm record_alloc loc p o ctxt =
  let op = ctxt.op_record in
  {
    ctxt with op_record = {
      op with
      gen = GenMap.add (loc,p) o op.gen
    }
  }

let%lm record_split loc p o1 o2 ctxt =
  let op = ctxt.op_record in
  { ctxt with op_record = {
      op with splits = SplitMap.add (loc,p) (o1,o2) op.splits
    }
  }

let alloc_split,alloc_ovar =
  let alloc_ovar_inner ctxt =
    { ctxt with
      ovars = ctxt.v_counter::ctxt.ovars;
      v_counter = ctxt.v_counter + 1 },OVar ctxt.v_counter
  in
  let alloc_split loc p o =
    let%bind o1 = alloc_ovar_inner
    and o2 = alloc_ovar_inner in
    add_constraint (Split (o,(o1,o2))) >>
    record_split loc p o1 o2 >>
    return (o1,o2)
  in
  let alloc_ovar loc p =
    let%bind o = alloc_ovar_inner in
    record_alloc loc p o >> return o
  in
  alloc_split,alloc_ovar

(* this must record *)
let lift_to_ownership loc root t_simp =
  let rec simple_lift ~unfld root =
    function
    | `Mu (id,t) when IntSet.mem id unfld ->
      let%bind t' = simple_lift ~unfld root t in
      return @@ Mu (id, t')
    | (`Mu (id,t) as mu) -> simple_lift ~unfld:(IntSet.add id unfld) root @@ unfold_simple id mu t
    | `Array `Int ->
      let%bind o = alloc_ovar loc root in
      return @@ Array (Int, o)
    | `Ref t ->
      let%bind o = alloc_ovar loc root in
      let%bind t' = simple_lift ~unfld (P.deref root) t in
      return @@ Ref (t',o)
    | `Int -> return Int
    | `TVar id -> return @@ TVar id
    | `Tuple tl ->
      let%bind tl' = mmapi (fun i t ->
          simple_lift ~unfld (P.t_ind root i) t
        ) tl in
      return @@ Tuple tl'
  in
  let%bind t = simple_lift ~unfld:IntSet.empty root t_simp in
  constrain_well_formed t >> return t

let mtmap p f tl =
  mmapi (fun i e -> f (P.t_ind p i) e) tl

(* This needs to record *)
let make_fresh_type loc root t =
  let rec loop root = function
  | Int -> return Int
  | Array (t,_) ->
    let%bind o' = alloc_ovar loc root in
    let%bind t' = loop (P.elem root) t in
    return @@ Array(t',o')
  | Ref (t,_) ->
    let%bind o' = alloc_ovar loc root in
    let%bind t' = loop (P.deref root) t in
    return @@ Ref(t',o')
  | TVar id -> return @@ TVar id
  | Tuple tl ->
    let%bind tl' = mtmap root loop tl in
    return @@ Tuple tl'
  | Mu (id,t) ->
    let%bind t' = loop root t in
    return @@ Mu (id,t')
  in
  let%bind t' = loop root t in
  constrain_well_formed t' >> return t'

let update_map v t m =
  SM.remove v m |> SM.add v t

let%lm update_type v t ctxt = {ctxt with gamma = update_map v t ctxt.gamma }

let%lq lkp v ctxt = StringMap.find v ctxt.gamma
let%lq lkp_ref v ctxt = match StringMap.find v ctxt.gamma with
  | Ref (t,o) -> (t,o)
  | _ -> failwith "Not a ref"
           
let%lq lkp_array v ctxt = match StringMap.find v ctxt.gamma with
  | Array (t,o) -> (t,o)
  | _ -> failwith "Not an array"

let map_type k v  =
  let%bind t = lkp v in
  let%bind (t',subt,subt') = k t in
  return @@ (update_type v t',subt,subt')

let fresh_ap e_id =
  let loc = MAlias e_id in
  function
  | AVar v ->
    map_type (fun t ->
        let%bind t' = make_fresh_type loc (P.var v) t in
        return (t',t,t')
      ) v
  | ADeref v ->
    map_type (function
      | Ref (t,o) ->
        let%bind t' = make_fresh_type loc (P.deref @@ P.var v) t in
        begin%m
            constrain_wf_loop o t';
             return (Ref (t',o),t,t')
        end
      | _ -> assert false
      ) v
  | AProj (v,ind) ->
    map_type (function
      | Tuple tl ->
        let t = List.nth tl ind in
        let%bind t' = make_fresh_type loc (P.t_ind (P.var v) ind) t in
        let tl' = update_nth tl ind t' in
        return (Tuple tl',t,t')
      | _ -> assert false
      ) v
  | APtrProj (v,ind) ->
    map_type (function
      | Ref (Tuple tl,o) ->
        let t = List.nth tl ind in
        let%bind t' = make_fresh_type loc (P.t_ind (P.deref @@ P.var v) ind) t in
        let tl' = update_nth tl ind t' in
        begin%m
            constrain_wf_loop o t';
             return (Ref (Tuple tl',o),t,t')
        end
      | _ -> assert false) v

(* this must record *)
let get_type_scheme e_id v ctxt =
  let st = IntMap.find e_id ctxt.iso.SimpleChecker.SideAnalysis.let_types in
  lift_to_ownership (MGen e_id) (P.var v) st ctxt

let tarray o t = Array (t,o)
let tref o t = Ref (t,o)

let rec split_type loc p =
  let split_mem o t ext k =
    let%bind (t1,t2) = split_type loc (ext p) t
    and (o1,o2) = alloc_split loc p o in
    begin%m
        constrain_wf_loop o1 t1;
         constrain_wf_loop o2 t2;
         return @@ (k o1 t1,k o2 t2)
    end
  in
  function
  | (Int as t)
  | (TVar _ as t) -> return (t,t)
  | Mu (id,t) ->
    let%bind (t1,t2) = split_type loc p t in
    return @@ (Mu (id,t1),Mu (id,t2))
  | Tuple tl ->
    let%bind split_list = mtmap p (split_type loc) tl in
    let (tl1,tl2) = List.split split_list in
    return @@ (Tuple tl1,Tuple tl2)
  | Ref (t,o) -> split_mem o t P.deref tref
  | Array (t,o) -> split_mem o t P.elem tarray


let%lm constrain_rel ~e_id ~rel ~src:t1 ~dst:t2 ctxt =
  let dst_unfld =
    let open SimpleChecker.SideAnalysis in
    if (IntSet.mem e_id ctxt.iso.unfold_locs) ||
       (IntSet.mem e_id ctxt.iso.fold_locs) then
      unfold t2
    else
      t2
  in
  let rec loop t1 t2 ctxt =
    match t1, t2 with
    | TVar _,TVar _
    | Int, Int -> ctxt
    | Ref (t1',o1), Ref (t2',o2)
    | Array (t1',o1), Array (t2',o2) ->
      loop t1' t2' { ctxt with ocons = (rel o1 o2)::ctxt.ocons }
    | Mu (_,t1'), Mu (_,t2') -> loop t1' t2' ctxt
    | Tuple tl1,Tuple tl2 ->
      List.fold_left2 (fun acc t1 t2 -> loop t1 t2 acc) ctxt tl1 tl2
    | _,_ -> failwith "Type mismatch (simple checker broken B?)"
  in
  loop t1 dst_unfld ctxt

let constrain_eq = constrain_rel ~rel:(fun o1 o2 -> Eq (o1,o2))

let constrain_write o = add_constraint @@ Write o

let%lm with_types bindings cont ctxt =
  let (ctxt',()) = cont {
      ctxt with gamma =
        List.fold_left (fun acc (k,t) ->
          SM.add k t acc
        ) ctxt.gamma bindings }
  in
  { ctxt' with gamma = List.fold_left (fun acc (k,_) ->
        SM.remove k acc
      ) ctxt'.gamma bindings }

let lkp_split loc v =
  let%bind t = lkp v in
  let%bind (t1,t2) = split_type loc (P.var v) t in
  update_type v t1 >> return t2

let%lq is_unfold eid ctxt =
  let open SimpleChecker.SideAnalysis in
  IntSet.mem eid ctxt.iso.unfold_locs

let%lq theta f ctxt = SM.find f ctxt.theta

let%lm sum_types t1 t2 out ctxt =
  let rec loop t1 t2 out ctxt =
    match t1,t2,out with
    | TVar _,TVar _,TVar _
    | Int,Int,Int -> ctxt
    | Mu (_,t1), Mu (_,t2), Mu (_,t3) -> loop t1 t2 t3 ctxt
    | Tuple tl1,Tuple tl2, Tuple tl3 ->
      fold_left3i (fun ctxt _ t1 t2 t3 -> loop t1 t2 t3 ctxt) ctxt tl1 tl2 tl3
    | Ref (t1,o1), Ref (t2,o2), Ref (out,oout)
    | Array (t1,o1), Array (t2,o2), Array (out,oout) ->
      loop t1 t2 out { ctxt with ocons = Split (oout,(o1,o2))::ctxt.ocons }
    | _,_,_ -> failwith "type mismatch (simple checker broken A?)"
  in
  loop t1 t2 out ctxt

let process_call e_id c =
  let%bind arg_types = mmap (lkp_split @@ SCall e_id) c.arg_names
  and fun_type = theta c.callee in
  begin%m
      miter (fun (i,a) -> constrain_eq ~e_id ~src:i ~dst:a) @@ List.combine arg_types fun_type.arg_types;
       miteri (fun i arg_name ->
         let%bind t = lkp arg_name in
         let%bind t' = make_fresh_type (MGen e_id) (P.var arg_name) t in
         let out_type = List.nth fun_type.output_types i in
         sum_types t out_type t' >> update_type arg_name t'
       ) c.arg_names;
       return fun_type.result_type
  end

let%lm save_type e_id ctxt =
  { ctxt with save_env = IntMap.add e_id ctxt.gamma ctxt.save_env }

let rec process_expr ?output ((e_id,_),expr) =
  save_type e_id >>
  match expr with
  | EVar v -> begin
      let%bind t2 = lkp_split (SRet e_id) v in
      match output with
      | None -> return ()
      | Some (output_types,return_type) ->
        begin%m
          constrain_eq ~e_id ~src:t2 ~dst:return_type;
          miter (fun (v,out_t) ->
            let%bind curr_t = lkp v in
            constrain_eq ~e_id ~src:curr_t ~dst:out_t
          ) output_types
        end
    end
  | Seq (e1,e2) ->
    begin%m process_expr e1; process_expr ?output e2 end
  | NCond (v,e1,e2) ->
    process_conditional ~e_id ~tr_branch:(
        let%bind t = lkp v in
        let%bind t' = make_fresh_type (MGen e_id) (P.var v) t in
        update_type v t'
      ) ?output e1 e2
  | Cond (_,e1,e2) ->
    process_conditional ~e_id ~tr_branch:(return ()) ?output e1 e2
  | Assign (v,IInt _,nxt) ->
    let%bind (t,o) = lkp_ref v in
    assert (t = Int);
    constrain_write o >> process_expr ?output nxt
  | Assign (v, IVar i,nxt) ->
    let%bind t2 = lkp_split (SBind e_id) i
    and (vt,o) = lkp_ref v in
    let%bind t = make_fresh_type (MGen e_id) (P.var v) (Ref (vt,o)) in
    let (vt',o') = match t with
      | Ref (vt',o') -> (vt',o')
      | _ -> assert false
    in
    begin%m
        constrain_wf_loop o' vt';
         constrain_eq ~e_id ~src:t2 ~dst:vt';
         update_type v @@ Ref (vt',o');
         constrain_write o;
         constrain_write o';
         process_expr ?output nxt
    end
  | Update (base,_,contents,nxt) ->
    let%bind (cts,o) = lkp_array base
    and new_cts = lkp_split (SBind e_id) contents in
    begin%m
         constrain_wf_loop o new_cts;
         constrain_write o;
         constrain_eq ~e_id ~src:cts ~dst:new_cts;
         update_type base @@ Array (new_cts,o);
         process_expr ?output nxt
    end
  | Alias(src,dst,nxt) ->
    let%bind (src_up,st,st') = fresh_ap e_id @@ AVar src
    and (dst_up,dt,dt') = fresh_ap e_id dst in
    begin%m
        shuffle_types ~e_id ~src:(st,st') ~dst:(dt,dt');
         src_up;
         dst_up;
         process_expr ?output nxt
    end
  | Assert (_,nxt) -> process_expr ?output nxt
  | Let (PVar v,Mkref (RVar src),body) ->
    let%bind t2 = lkp_split (SBind e_id) src in
    begin
      match%bind get_type_scheme e_id v with
      | (Ref (ref_cont,o)) as t' ->
        begin%m
            constrain_eq ~e_id ~src:t2 ~dst:ref_cont;
             add_constraint @@ Write o;
             with_types [(v,t')] @@ process_expr ?output body
        end
      | _ -> assert false
    end
  | Let (PVar v,(Null | MkArray _),body) ->
    let%bind t = get_type_scheme e_id v in
    with_types [(v,t)] @@ process_expr ?output body
  | Let (PVar v,Mkref (RNone | RInt _), body) ->
    let%bind new_var = alloc_ovar (MGen e_id) (P.var v) in
    begin%m
        add_constraint @@ Write new_var;
         with_types [(v,Ref (Int, new_var))] @@ process_expr ?output body
    end
  | Let (patt,rhs,body) ->
    let%bind to_bind =
      match rhs with
      | Var v -> lkp_split (SBind e_id) v
      | LengthOf _
      | Nondet _
      | Const _ -> return Int
      (* these two cases are handled above *)
      | Null -> assert false
      | MkArray _ -> assert false
      | Read (v,_) ->
        let%bind (t_cont,o) = lkp_array v in
        let%bind (t_cont1,t_cont2) = split_type (SBind e_id) (P.elem (P.var v)) t_cont in
        begin%m
            update_type v @@ Array (t_cont1,o);
             return t_cont2
        end
      | Deref v -> 
        let%bind (t,o) = lkp_ref v in
        let%bind (t1,t2_pre) = split_type (SBind e_id) (P.deref (P.var v)) t in
        let%bind uf = is_unfold e_id in
        let t2 =
          if uf then
            unfold t2_pre
          else
            t2_pre
        in
        begin%m
          update_type v @@ Ref (t1,o);
             return t2
        end
      | Mkref (RVar _) ->
      (* this should not be possible *)
        assert false
      | Mkref (RNone | RInt _) ->
        return @@ Ref (Int, OConst 1.0)
      | Tuple t_init ->
        let%bind tl = mmap (fun k ->
            match k with
            | RNone
            | RInt _ -> return Int
            | RVar v ->
              let%bind t = lkp v in
              let%bind (t1,t2) = split_type (SBind e_id) (P.var v) t in
              update_type v t1 >> return t2
          ) t_init in
        return @@ Tuple tl
      | Call c -> process_call e_id c
    in
    let rec assign_patt_loop acc patt ty =
      match patt,ty with
      | PVar v,_ -> (v,ty)::acc
      | PNone, _ -> acc
      | PTuple pl,Tuple tl ->
        List.fold_left2 assign_patt_loop acc pl tl
      | PTuple _,_ -> assert false
    in
    let bindings = assign_patt_loop [] patt to_bind in
    with_types bindings @@ process_expr ?output body
and process_conditional ~e_id ~tr_branch ?output e1 e2 ctxt =
  let (ctxt_tpre,()) = tr_branch ctxt in
  let (ctxt_t,()) = process_expr ?output e1 ctxt_tpre in
  let (ctxt_f,()) = process_expr ?output e2 { ctxt_t with gamma = ctxt.gamma } in
  assert (StringMap.for_all (fun k _ -> StringMap.mem k ctxt_t.gamma) ctxt_f.gamma);
  assert (StringMap.for_all (fun k _ -> StringMap.mem k ctxt_f.gamma) ctxt_t.gamma);
  miter (fun (k,ft) ->
    let%bind t' = make_fresh_type (MJoin e_id) (P.var k) ft in
    let tt = StringMap.find k ctxt_t.gamma in
    let constrain_ge = constrain_rel ~rel:(fun o1 o2 -> Ge (o1, o2)) in
    begin%m
        constrain_ge ~e_id ~src:tt ~dst:t';
         constrain_ge ~e_id ~src:ft ~dst:t';
         update_type k t'
    end
  ) (StringMap.bindings ctxt_f.gamma) { ctxt_f with gamma = StringMap.empty }

module Result = struct
  type t = {
    ocons: ocon list;
    ovars: int list;
    op_record: ownership ownership_ops;
    ty_envs: otype StringMap.t IntMap.t;
    theta : (otype RefinementTypes._funtype) StringMap.t;
  }
end

let analyze_fn ctxt fn =
  let arg_names = fn.args in
  let fn_type = SM.find fn.name ctxt.theta in
  let start_gamma = SM.of_bindings @@ List.combine arg_names fn_type.arg_types in
  let out_type = List.combine arg_names fn_type.output_types in
  let (ctxt,()) = process_expr ~output:(out_type,fn_type.result_type) fn.body { ctxt with gamma = start_gamma } in
  { ctxt with gamma = SM.empty }

let infer (simple_types,iso) intr (fn,prog) =
  let lift_plist loc l =
    mmapi (fun i t ->
      lift_to_ownership loc (P.arg i) t
    ) l
  in   
  let lift_simple_ft nm ft =
    let%bind arg_types = lift_plist (MArg nm) ft.SimpleTypes.arg_types
    and output_types = lift_plist (MOut nm) ft.SimpleTypes.arg_types
    and result_type = lift_to_ownership (MRet nm) P.ret ft.SimpleTypes.ret_type in
    return RefinementTypes.{ arg_types; output_types; result_type }
  in
  let rec lift_reft loc p =
    let module R = RefinementTypes in
    function
    | R.Int _ -> return Int
    | R.TVar id -> return @@ TVar id
    | R.Tuple (_,tl) ->
      let%bind tl' = mtmap p (lift_reft loc) tl in
      return @@ Tuple tl'
    | R.Mu (_,_,id,t) ->
      let%bind t' = lift_reft loc p t in
      return @@ Mu (id,t')
    | R.Ref (_,_,_) -> failwith "Unexpected mem type in intrinsic"
    | R.Array (_,_,_,_) -> failwith "unexpected array type in intrinsic"
  in
  let lift_refp loc l =
    mmapi (fun i t ->
      lift_reft loc (P.arg i) t
    ) l
  in
  let lift_intrinsic_type nm ft =
    let open RefinementTypes in
    let%bind arg_mapped = lift_refp (MArg nm) ft.arg_types
    and out_mapped = lift_refp (MOut nm) ft.output_types
    and ret_type = lift_reft (MRet nm) P.ret ft.result_type in
    return {
      arg_types = arg_mapped;
      output_types = out_mapped;
      result_type = ret_type
    }
  in
  let init_context = {
    ovars = [];
    v_counter = 0;
    iso;
    ocons = [];
    gamma = SM.empty;
    theta = SM.empty;
    op_record = {
      splits = SplitMap.empty;
      gen = GenMap.empty
    };
    save_env = IntMap.empty
  } in
  let ctxt =
    SM.fold (fun nm st acc ->
      let (acc,ft) = lift_simple_ft nm st acc in
      { acc with theta = SM.add nm ft acc.theta }
    ) simple_types init_context
    |> SM.fold (fun nm it acc ->
        let (acc,ft) = lift_intrinsic_type nm it acc in
        { acc with theta = SM.add nm ft acc.theta }
      ) intr 
  in
  let ctxt = List.fold_left analyze_fn ctxt fn in
  let (ctxt,_) = process_expr prog ctxt in
  {
    Result.ocons = ctxt.ocons;
    Result.ovars = ctxt.ovars;
    Result.op_record = ctxt.op_record;
    Result.ty_envs = ctxt.save_env;
    Result.theta = ctxt.theta
  }

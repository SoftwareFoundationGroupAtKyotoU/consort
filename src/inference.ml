open Ast
open RefinementTypes
open Sexplib.Std
    
module SM = StringMap
module SS = Set.Make(String)
module P = Paths

type concr_ap = P.concr_ap

let loc_to_string =
  let labeled_expr s i = Printf.sprintf "%s@%d" s i in
  let fn_loc fn l = Printf.sprintf "fn %s %s" fn l in
  function
  | LCond i -> labeled_expr "if" i
  | LArg f -> fn_loc f "Arg"
  | LReturn f -> fn_loc f "Ret"
  | LOutput f -> fn_loc f "Out"
  | LAlias i -> labeled_expr "alias" i
  | LLet i -> labeled_expr "let" i
  | LCall i -> labeled_expr "call" i

type pred_context = {
  fv: refine_ap list;
  loc: pred_loc;
  target_var: concr_ap
}

type funenv = funtype SM.t
type tenv = typ SM.t

type ownership_type = (unit, float) RefinementTypes._typ
type o_theta = ownership_type RefinementTypes._funtype StringMap.t
type o_solution = ((int,ownership_type StringMap.t) Hashtbl.t * o_theta)

type oante =
  | ORel of ownership * [ `Eq | `Ge | `Gt ] * float
  | OAny of oante list [@@deriving sexp]

let sexp_of_tenv = SM.sexp_of_t ~v:sexp_of_typ

type tcon = {
  env: (Paths.concr_ap * concr_refinement) list;
  ante: concr_refinement;
  conseq: concr_refinement;
  owner_ante: oante list;
}[@@deriving sexp]

type ocon =
  (* Constraint ownership variable n to be 1 *)
  | Write of ownership
  (* ownership has to be greater than 0 *)
  | Live of ownership
  (* ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Shuff of (ownership * ownership) * (ownership * ownership)
  | Split of ownership * (ownership * ownership)
  | Eq of ownership * ownership

module IntMap = Map.Make(struct
    type t = int
    let compare n1 n2 = n1 - n2
  end)

type context = {
  theta: funenv;
  gamma: tenv;
  ownership: ocon list;
  ovars: int list;
  refinements: tcon list;
  pred_arity: int IntMap.t;
  v_counter: int;
  pred_detail: (int,pred_context) Hashtbl.t;
  store_env: int -> tenv -> unit;
  o_info: o_solution
}

module Result = struct
  type t = {
    theta: funenv;
    ownership: ocon list;
    ovars: int list;
    refinements: tcon list;
    arity: int IntMap.t;
    ty_envs: (int,tenv) Hashtbl.t
  }
end

let alloc_ovar ctxt =
  ({ ctxt with v_counter = ctxt.v_counter + 1; ovars = ctxt.v_counter::ctxt.ovars }, OVar ctxt.v_counter)

let (>>) f g = fun st ->
  let (st',v1) = f st in
  let (st'', v2) = g st' in
  (st'',(v1, v2))

let add_owner_con l ctxt = { ctxt with ownership = l @ ctxt.ownership  }

let update_map v t m =
  SM.remove v m
  |> SM.add v t

let update_type v t ctxt =
  { ctxt with gamma = update_map v t ctxt.gamma }

let add_type v t ctxt =
  let te =
    SM.add v t ctxt.gamma
  in
  { ctxt with gamma = te }

let rec denote_type path (bind: (int * Paths.concr_ap) list) acc t =
  match t with
  | Ref (t',_) -> denote_type (`ADeref path) bind acc t'
  | Int r ->
    let comp_r = compile_refinement path bind r in
    (path,comp_r)::acc
  | Tuple (b,t) ->
    let (bind' : (int * Paths.concr_ap) list) = (subst_of_binding path b) @ bind in
    List.mapi (fun i te -> (i,te)) t
    |> List.fold_left (fun acc (i,te) ->
        denote_type (`AProj (path,i)) bind' acc te
      ) acc

let denote_gamma gamma =
  SM.fold (fun v t acc ->
    denote_type (`AVar v) [] acc t
  ) gamma []

let rec split_ref_type ctxt (t,o) =
  let (ctxt,(o1,o2)) = (alloc_ovar >> alloc_ovar) ctxt in
  let (ctxt',(t1,t2)) = split_type ctxt t in
  let t1' = Ref (t1,o1) in
  let t2' = Ref (t2,o2) in
  (add_owner_con [Split (o,(o1, o2))] ctxt', (t1', t2'))
and split_type ctxt t =
  match t with
  | Int _ -> (ctxt, (t,t))
  | Ref (t,o) ->
    split_ref_type ctxt (t,o) 
  | Tuple (b,tl) ->
    let (ctxt',tl1,tl2) = List.fold_right (fun t' (ctxt',tl1,tl2) ->
        let (ctxt'',(t'1,t'2)) = split_type ctxt' t' in
        (ctxt'', t'1::tl1,t'2::tl2)
      ) tl (ctxt,[],[])
    in
    (ctxt',(Tuple (b,tl1),Tuple (b,tl2)))

let rec split_type_with arg_t in_t =
  match arg_t,in_t with
  | Int _,Int _ -> (arg_t,arg_t)
  | Ref (arg_t',OConst o1),Ref (in_t',in_o) -> begin
      assert ((Pervasives.compare in_o o1) <= 0);
      let (arg_t'1,arg_t'2) = split_type_with arg_t' in_t' in
      Ref (arg_t'1,OConst (o1 -. in_o)),Ref (arg_t'2, OConst in_o)
    end
  | Ref (_,OVar _),_ -> failwith "Found free ovar in split type"
  | Tuple (b,arg_tl), Tuple (_,tl_o) ->
    let (arg_tl1,arg_tl2) =
      List.map2 split_type_with arg_tl tl_o
      |> List.split
    in
    Tuple (b,arg_tl1), Tuple (b,arg_tl2)
  | _ -> assert false

let split_arg i c_name ctxt arg_t =
  let (_,o_th) = ctxt.o_info in
  if not @@ SM.mem c_name o_th then
    split_type ctxt arg_t
  else
    let { arg_types; _ } = SM.find c_name o_th in
    let in_t = List.nth arg_types i in
    (ctxt,split_type_with arg_t in_t)

let add_constraint gamma ctxt ?(o=[]) ante conseq =
  { ctxt with
    refinements = {
      env = gamma;
      ante;
      conseq;
      owner_ante = o;
    }::ctxt.refinements
  }

let rec constrain_owner t1 t2 ctxt =
  match t1,t2 with
  | Ref (r1,o1),Ref (r2,o2) ->
    add_owner_con [Eq (o1,o2)] ctxt
    |> constrain_owner r1 r2
  | Int _,Int _ -> ctxt
  | Tuple (_,tl1), Tuple (_,tl2) ->
    List.fold_left2 (fun c te1 te2 ->
        constrain_owner te1 te2 c
      ) ctxt tl1 tl2
  | _ -> assert false

let add_type_implication gamma t1_ t2_ ctxt_ =
  let rec impl_loop ctxt t1 t2 =
    match t1,t2 with
    | Int r1, Int r2 -> add_constraint gamma ctxt r1 r2
    | Ref (t1',_), Ref (t2',_) -> impl_loop ctxt t1' t2'
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 impl_loop ctxt tl1 tl2
    | _ -> assert false
  in
  impl_loop ctxt_ t1_ t2_

let add_var_implication dg gamma var t ctxt =
  add_type_implication dg (compile_type (SM.find var gamma) var) (compile_type t var) ctxt

let ap_is_target target sym_vals ap =
  match ap with
  | #Paths.concr_ap as cr_ap -> cr_ap = target
  | `Sym i -> (List.assoc i sym_vals) = target

let filter_fv path sym_vals fv =
  List.filter (fun free_var -> not @@ ap_is_target path sym_vals free_var) fv

let alloc_pred ~loc (fv,target_var,sym_vals) ctxt =
  let n = ctxt.v_counter in
  let target_in_fv =
    List.exists (fun free_var ->
      ap_is_target target_var sym_vals free_var) fv
  in
  (*  Printf.printf "%d: is %s included in fv? %b\n" n (refine_ap_to_string target_var) target_in_fv;*)
  let arity = (List.length fv) -
      (if target_in_fv then 1 else 0) + 1 + !KCFA.cfa (* 1 for nu and k for context *)
  in
  (*  Printf.printf "%d: New arity: %d\n" n arity;*)
  Hashtbl.add ctxt.pred_detail n { fv = (fv :> refine_ap list); loc; target_var };
  ({ ctxt with
     v_counter = n + 1;
     pred_arity = IntMap.add n arity ctxt.pred_arity
   }, n)
    

let make_fresh_pred ~pred_vars:((fv,target,s_val) as pred_vars) ~loc ctxt =
  let (ctxt',p) = alloc_pred ~loc pred_vars ctxt in
  (ctxt',Pred (p,filter_fv target s_val fv))

let rec free_vars_contains_v (r: concr_refinement) v =
  let has_var = function
    | #concr_ap as cp -> Paths.has_var v cp
  in
  let imm_is_var ri = match ri with RConst _ -> false | RAp ap -> Paths.has_var v (ap :> concr_ap) in
  match r with
  | Pred (_,(pv,_))
  | NamedPred (_,(pv,_))
  | CtxtPred (_,_,(pv,_)) -> List.exists has_var pv
  | Relation { rel_op1 = op1; rel_op2 = op2; _ } ->
    imm_is_var op2 || (match op1 with
      RImm v -> imm_is_var v | Nu -> false)
  | And (r1, r2) -> free_vars_contains_v r1 v || free_vars_contains_v r2 v
  | _ -> false

let free_vars_contains ss r =
  SS.exists (free_vars_contains_v r) ss

let predicate_vars kv =
  List.fold_left (fun acc (k, t) ->
      match t with
      | Int _ -> (`AVar k)::acc
      | _ -> acc
  ) [] kv |> List.rev

let gamma_predicate_vars gamma =
  SM.bindings gamma |> predicate_vars

let with_type t ctxt = (ctxt,t)

let t_var_counter = ref 0;;

let fresh_tvar () =
  let v = !t_var_counter in
  incr t_var_counter;
  v

let lift_src_ap = function
  | AVar v -> `AVar v
  | ADeref v -> `ADeref (`AVar v)
  | AProj (v,i) -> `AProj (`AVar v,i)
  | APtrProj (v,i) -> `AProj (`ADeref (`AVar v), i)

let remove_var_from_pred ~loc ~curr_te ~to_remove path (sym_vars,sym_val) r context =
  let curr_comp = compile_refinement path sym_val r in
  if free_vars_contains to_remove curr_comp then
    let (ctxt',new_pred) = make_fresh_pred ~loc ~pred_vars:(sym_vars,path,sym_val) context in
    let new_comp = compile_refinement path sym_val new_pred in
    let ctxt'' = add_constraint curr_te ctxt' curr_comp new_comp in
    (ctxt'',new_pred)
  else
    (context,r)

let remove_var_from_type ~loc ~curr_te ~to_remove root_var in_scope t context =
  let staged = remove_var_from_pred ~loc ~curr_te ~to_remove in
  walk_with_bindings staged root_var (in_scope,[]) t context

let remove_var ~loc to_remove ctxt =
  let curr_te = denote_gamma ctxt.gamma in
  let in_scope = SM.bindings ctxt.gamma |> List.filter (fun (k,_) -> not (SS.mem k to_remove)) |> predicate_vars in
  let remove_fn = remove_var_from_type ~loc ~curr_te ~to_remove in
  let updated =
    SM.fold (fun v_name t c ->
      if SS.mem v_name to_remove then
        c
      else
        let (c',t') = remove_fn (`AVar v_name) in_scope t c in
        { c' with gamma = SM.add v_name t' c'.gamma }
    ) ctxt.gamma { ctxt with gamma = SM.empty }
  in
  updated

let lift_imm_op_to_rel = function
  | IVar v -> RAp (`AVar v)
  | IInt n -> RConst n

let lift_relation { rop1; cond; rop2 } =
  Relation { rel_op1 = RImm (lift_imm_op_to_rel rop1); rel_cond = cond; rel_op2 = lift_imm_op_to_rel rop2 }

let _dump_env ?(msg) tev =
  (match msg with
  | Some m -> print_endline m;
  | None -> ());
  sexp_of_tenv tev |> Sexplib.Sexp.to_string_hum |> print_endline

let rec strengthen_eq ~strengthen_type ~target =
  match strengthen_type with
  | Int r ->
    let r' = And (r,Relation {
          rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp target
        })
    in
    Int r'
  | Ref _ -> strengthen_type
  | Tuple (b,tl) ->
    let tl' = List.mapi (fun i t ->
        strengthen_eq ~strengthen_type:t ~target:(Paths.t_ind target i)
      ) tl in
    Tuple (b,tl')

type walk_ctxt = {
  o_stack: ownership list;
  binding: (int * concr_ap) list;
  path: concr_ap;
}

let step_tup wc b i t =
  ({ wc with
    path = `AProj (wc.path,i);
    binding = (subst_of_binding wc.path b) @ wc.binding;
  },t)

let step_ref wc o t =
  ({
    wc with
    path = `ADeref wc.path;
    o_stack = o::wc.o_stack
  },t)

let ctxt_compile_ref wc =
  compile_refinement wc.path wc.binding

let fold_left3i f a l1 l2 l3 =
  let rec inner_loop i acc l1 l2 l3 =
    match l1,l2,l3 with
    | h1::t1,h2::t2,h3::t3 ->
      inner_loop (i+1) (f acc i h1 h2 h3) t1 t2 t3
    | [],[],[] -> acc
    | _ -> raise @@ Invalid_argument "differing lengths"
  in
  inner_loop 0 a l1 l2 l3

let constrain_heap_path (cmp: [< `Ge | `Gt | `Eq]) =
  List.map (fun o -> ORel (o,cmp,0.0))

let ctxt_gt wc = constrain_heap_path `Gt wc.o_stack
let ctxt_any_eq wc =
  match wc.o_stack with
  (* just false *)
  | [] -> [ORel (OConst 1.0,`Eq,0.0)]
  | l -> [OAny (constrain_heap_path `Eq l)]

let all_const_o ctxt =
  List.for_all (function
  | OConst _ -> true
  | _ -> false) ctxt.o_stack

let all_live_o ctxt =
  List.for_all (function
  | OConst o -> o > 0.0
  | _ -> failwith "Called with symbolic ownership path") ctxt.o_stack

let unsafe_extract_pred = function
  | Pred (i,(fv,_)) -> (i,fv)
  | _ -> failwith "You broke an invariant somewhere I guess :("

let combine_concr_preds (c1,ct1) (c2,ct2) c_out =
  let out_live = all_live_o c_out in
  let t1_live = all_live_o c1 in
  let t2_live = all_live_o c2 in
  if (not out_live) || ((not t1_live) && (not t2_live)) then
    Top
  else if t1_live && t2_live then
    And (ct1,ct2)
  else if t1_live then
    ct1
  else
    (assert t2_live; ct2)

let generalize_pred root out_type combined_pred =
  let rec gen_ap_loop ap ~exc ~k =
    if ap = root then
      k (root :> refine_ap) out_type
    else
      match ap with
      | `AVar v -> exc (`AVar v)
      | `ADeref ap' ->
        gen_ap_loop ap'
          ~exc:(fun _ -> failwith "Free deref rooted outside target")
          ~k:(fun _ t ->
            match t with
            | Ref (t',_) -> k (ap :> refine_ap) t'
            | _ -> assert false)
      | `AProj (ap',i) -> 
        gen_ap_loop ap'
          ~exc:(fun _ -> (ap :> refine_ap))
          ~k:(fun _ t ->
            match t with
            | Tuple (b,tl) ->
              let (s,_) = List.find (fun (_,sym_ap) ->
                  match sym_ap with
                  | SProj i' when i' = i -> true
                  | _ -> false) b in
              k (`Sym s) (List.nth tl i)
            | _ -> assert false
          )
  in
  let gen_ap ap = gen_ap_loop ap ~exc:(fun t -> t) ~k:(fun ap _ -> ap) in
  let rec gen_loop = function
    | Top -> Top
    | ConstEq n -> ConstEq n
    | And (r1,r2) -> And (gen_loop r1,gen_loop r2)
    | Relation r -> Relation r
    | Pred (i,(fv,_)) -> Pred (i,List.map gen_ap fv)
    | CtxtPred (i1,i2,(fv,_)) -> CtxtPred (i1,i2,List.map gen_ap fv)
    | NamedPred (nm,(fv,_)) -> NamedPred (nm,List.map gen_ap fv)
  in
  gen_loop combined_pred

(* apply_matrix walks t1, t2 and out_type in parallel. At each leaf
   node, it generates a constrain on out_type's refinements based
   on the ownerships along the paths from the roots of t1 and t2 to the leaf.
*)
let apply_matrix ~t1 ?(t2_bind=[]) ~t2 ?(force_cons=true) ~out_root ?(out_bind=[]) ~out_type ctxt =
  let g = denote_gamma ctxt.gamma in
  let rec inner_loop (c1,t1) (c2,t2) (c_out,out_t) ctxt =
    match t1,t2,out_t with
    | Tuple (b1,tl1), Tuple (b2,tl2), Tuple (b_out,tl_out) ->
      let st1 = step_tup c1 b1 in
      let st2 = step_tup c2 b2 in
      let st3 = step_tup c_out b_out in
      fold_left3i (fun c ind t1' t2' t_out' ->
        inner_loop
          (st1 ind t1')
          (st2 ind t2')
          (st3 ind t_out')
          c
      ) ctxt tl1 tl2 tl_out
    | Ref (t1',o1), Ref (t2',o2), Ref (t_out',o_out) ->
      inner_loop
        (step_ref c1 o1 t1')
        (step_ref c2 o2 t2')
        (step_ref c_out o_out t_out')
        ctxt
    | Int r1,Int r2,Int out_r ->
      let gen_constraint =
        (force_cons) ||
        (not @@ List.for_all all_const_o [c1; c2; c_out])
      in
      let c_out_r = ctxt_compile_ref c_out out_r in
      let c_r1 = ctxt_compile_ref c1 r1 in
      let c_r2 = ctxt_compile_ref c2 r2 in
      if gen_constraint then
        let mk_constraint oante ante =
          {
            env = g;
            ante = ante;
            conseq = c_out_r;
            owner_ante = (ctxt_gt c_out) @ oante
          }
        in
        let cons = [
          mk_constraint ((ctxt_gt c1) @ (ctxt_gt c2)) @@ And (c_r1,c_r2);
          mk_constraint ((ctxt_any_eq c1) @ (ctxt_gt c2)) @@ c_r2;
          mk_constraint ((ctxt_gt c1) @ (ctxt_any_eq c2)) @@ c_r1
        ] in
        let (ctxt',d_list) = ctxt in
        ({ ctxt' with refinements =
             cons @ ctxt'.refinements },d_list)
      else
        let (i,_) = unsafe_extract_pred c_out_r in
        let comb_pred = combine_concr_preds (c1,c_r1) (c2,c_r2) c_out in
        let gen_pred = generalize_pred out_root out_type comb_pred in
        let (ctxt',d_list) = ctxt in
        (ctxt',(i,gen_pred)::d_list)
    | _ -> raise @@ Invalid_argument "Mismatched types"
  in
  let mk_ctxt b t =
    ({
      path = out_root;
      binding = b;
      o_stack = []
    },t)
  in
  inner_loop
    (mk_ctxt [] t1)
    (mk_ctxt t2_bind t2)
    (mk_ctxt out_bind out_type)
    (ctxt,[])

let rec push_subst bind = function
  | Int r ->
    let sigma = List.map (fun (i,v) -> (i,`AVar v)) bind in
    Int (partial_subst sigma r)
  | Ref (t,o) -> Ref (push_subst bind t,o)
  | Tuple (b,tl) ->
    let b_ext = List.map (fun (i,v) -> (i,SVar v)) bind in
    Tuple (b_ext @ b, tl)

let sub_pdef =
  function
  | [] -> (fun t -> t)
  | sub_assoc ->
    map_refinement (function
      | Pred (i,_) when List.mem_assoc i sub_assoc -> List.assoc i sub_assoc
      | r -> r)
                     

let rec assign_patt ~let_id ?(count=0) ctxt p t =
  match p,t with
  | PNone, _ -> (count,ctxt,p)
  | PVar v,_ -> (count,add_type v t ctxt,p)
  | PTuple t_patt,Tuple (b,tl) ->
    let (count',closed_patt) = List.fold_right2 (fun p t (c_acc,p_acc) ->
        match p,t with
        | PNone, Int _ ->
          let t_name = Printf.sprintf "__t_%d_%d" let_id c_acc in
          (succ c_acc,(PVar t_name)::p_acc)
        | _ -> (c_acc,p::p_acc)
      ) t_patt tl (count,[]) in
    let var_subst = List.map (fun (sym_var,b) ->
        match b with
        | SVar v -> (sym_var,v)
        | SProj i ->
          let bound_var =
            match List.nth closed_patt i with
            | PVar v -> v
            | _ -> assert false
          in
          (sym_var,bound_var)
      ) b in
    let (count',ctxt',t_patt') = List.fold_left2 (fun (count_acc,ctxt_acc,patt_acc) sub_p sub_t ->
        let (id,ctxt,p) = assign_patt ~let_id ~count:count_acc ctxt_acc sub_p @@ push_subst var_subst sub_t in
        (id,ctxt,p::patt_acc)
      ) (count',ctxt,[]) closed_patt tl in
    (count',ctxt',PTuple (List.rev t_patt'))
  | _ -> assert false

let rec collect_bound_vars acc patt =
  match patt with
  | PVar v -> SS.add v acc
  | PTuple pl -> List.fold_left collect_bound_vars acc pl
  | PNone -> acc

let o_map f o = match o with
  | Some d -> Some (f d)
  | None -> None

(* t is the type of the location on the RHS that is being bound (and destructed
   by assignment to patt *)
let rec strengthen_type ?root t patt ctxt =
  let maybe_strengthen_patt v ctxt' =
    match root with
    | None -> ctxt
    | Some p ->
      let t' = SM.find v ctxt'.gamma in
      ctxt'
      |> update_type v @@ strengthen_eq ~strengthen_type:t' ~target:p
  in
  match t,patt with
  | Int _,PVar v ->
    maybe_strengthen_patt v ctxt
    |> with_type @@ strengthen_eq ~strengthen_type:t ~target:(`AVar v)
  | Ref _,_ ->
    (ctxt,t)
  | Tuple (b,tl),PVar v ->
    let tl' = List.mapi (fun i t ->
        strengthen_eq ~strengthen_type:t ~target:(`AProj ((`AVar v),i))
      ) tl in
    maybe_strengthen_patt v ctxt
    |> with_type @@ Tuple (b,tl')
  | Tuple (b,tl),PTuple pl ->
    let ind_tl = List.mapi (fun i t -> (i,t)) tl in
    let (ctxt',tl') = List.fold_right2 (fun (i,t) p (ctxt_acc,tl_acc) ->
        let sub_root = o_map (fun r -> Paths.t_ind r i) root in
        let (c_acc',t') = strengthen_type ?root:sub_root t p ctxt_acc in
        (c_acc', t'::tl_acc)
      ) ind_tl pl (ctxt,[]) in
    (ctxt', Tuple (b,tl'))
  | _ -> failwith "mismatched types"

let rec strengthen_let patt rhs ctxt =
  let lkp_ref v = match SM.find v ctxt.gamma with
    | Ref (r,o) -> (r,o)
    | _ -> failwith "not a ref"
  in
  match patt,rhs with
  | PNone,_ -> ctxt
  | _,Const _
  | _,Mkref RNone
  | _,Mkref (RInt _)
  | _,Nondet
  | _,Call _ -> ctxt
  | _,Var v ->
    let t = SM.find v ctxt.gamma in
    let (ctxt',t') = strengthen_type ~root:(`AVar v) t patt ctxt in
    update_type v t' ctxt'
  | _,Deref v ->
    let (t,o) = lkp_ref v in
    let (ctxt',t') = strengthen_type t patt ctxt in
   update_type v (Ref (t',o)) ctxt'
  | (PVar v),Mkref (RVar v') ->
    let (t,o) = lkp_ref v in
    let t' = strengthen_eq ~strengthen_type:t ~target:(`AVar v') in
    update_type v (Ref (t',o)) ctxt
  | (PTuple pl),Tuple vl ->
    (* .... why would you do this? *)
    List.fold_left2 (fun acc p_sub i_lit ->
        match i_lit with
        | RInt _ | RNone -> acc
        | RVar v -> strengthen_let p_sub (Var v) acc
      ) ctxt pl vl
  | (PVar v),Tuple vl ->
    let pt = SM.find v ctxt.gamma in
    let rec collect ind c tl vl =
      match tl,vl with
      | [],[] -> ([],c)
      | (e_t::ttl,RNone::tvl) | (e_t::ttl,RInt _::tvl) ->
        let (tl',c') = collect (ind + 1) c ttl tvl in
        (e_t::tl',c')
      | (e_t::ttl,(RVar v')::tvl) ->
        let (tl',c') = collect (ind + 1) c ttl tvl in
        let v_type = SM.find v' ctxt.gamma in
        let vt' = strengthen_eq ~strengthen_type:v_type ~target:(`AProj ((`AVar v),ind)) in
        let e_t' = strengthen_eq ~strengthen_type:e_t ~target:(`AVar v') in
        (e_t'::tl', update_type v' vt' c')
      | _ -> failwith "type and value lengths don't match"
    in
    begin
      match pt with
      | Tuple (b,tl) ->
        let (tl',c') = collect 0 ctxt tl vl in
        update_type v (Tuple (b,tl')) c'
      | _ -> failwith "not a tuple type?"
    end
  | _ -> failwith "impossible"


let rec shuffle_owners t1 t2 t1' t2' ctxt =
  match t1,t2,t1',t2' with
  | Int _,Int _,Int _,Int _ -> ctxt
  | Ref (r1,o1),Ref (r2,o2), Ref (r1',o1'), Ref(r2',o2') ->
    shuffle_owners r1 r2 r1' r2' @@
      { ctxt with
        ownership = Shuff ((o1,o2),(o1',o2')) :: ctxt.ownership }
  | Tuple (_,tl1), Tuple (_,tl2), Tuple (_,tl1'), Tuple (_,tl2') ->
    let orig_tl = List.combine tl1 tl2 in
    let new_tl = List.combine tl1' tl2' in
    List.fold_left2 (fun ctxt' (te1,te2) (te1',te2') ->
      shuffle_owners te1 te2 te1' te2' ctxt'
    ) ctxt orig_tl new_tl
  | _ -> assert false

let rec post_update_type = function
  | Int _ -> false
  | Tuple (_,tl) -> List.exists post_update_type tl
  | Ref _ -> true

let rec sum_ownership t1 t2 out ctxt =
  match t1,t2,out with
  | Int _, Int _, Int _ -> ctxt
  | Ref (r1,o1), Ref (r2,o2), Ref (ro,oo) ->
    sum_ownership r1 r2 ro
      { ctxt with ownership = (Split (oo,(o1,o2)))::ctxt.ownership}
  | Tuple (_,tl1), Tuple (_,tl2), Tuple (_,tl_out) ->
    fold_left3i (fun ctxt _ e1 e2 e_out ->
        sum_ownership e1 e2 e_out ctxt) ctxt tl1 tl2 tl_out
  | _ -> assert false

let remove_sub ps ctxt =
  List.fold_left (fun c (i,_) ->
    { c with pred_arity =
        IntMap.remove i c.pred_arity }) ctxt ps

let rec meet_loop t_ref t_own =
  match t_ref,t_own with
  | Int r,Int () -> Int r
  | Ref (t_ref',_),Ref (t_own',o) ->
    Ref (meet_loop t_ref' t_own', OConst o)
  | Tuple (b,tl_ref), Tuple (_,tl_own) ->
    let tl_ref_cons = List.map2 meet_loop tl_ref tl_own in
    Tuple (b,tl_ref_cons)
  | _ -> failwith "Inconsistent type shapes"

let meet_ownership st_id (o_envs,_) ap t =
  if not (Hashtbl.mem o_envs st_id) then
    t
  else
    let o_env = Hashtbl.find o_envs st_id in
    map_ap ap (fun o_typ ->
      meet_loop t o_typ) (fun s -> SM.find s o_env)

let meet_gamma st_id o_info =
  SM.mapi (fun v t ->
    meet_ownership st_id o_info (`AVar v) t)

let meet_out i callee ctxt t =
  let (_,o_th) = ctxt.o_info in
  if not @@ SM.mem callee o_th then
    t
  else
    let { output_types; _  } = SM.find callee o_th in
    meet_loop t @@ List.nth output_types i

let rec process_expr ?output_type ?(remove_scope=SS.empty) ctxt (e_id,e) =
  let lkp v = SM.find v ctxt.gamma in
  let lkp_ref v = match lkp v with
    | Ref (r,o) -> (r,o)
    | _ -> failwith "Not actually a ref"
  in
  ctxt.store_env e_id @@ meet_gamma e_id ctxt.o_info ctxt.gamma;
  match e with
  | EVar v ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp v in
    let ctxt'' = update_type v t1 ctxt' in
    begin
      let c_type t = compile_type t "<ret>" in
      match output_type with
      | Some t ->
        let dg = denote_type (`AVar "<ret>") [] (denote_gamma ctxt''.gamma) t2 in
        add_type_implication dg (c_type t2) (c_type t) ctxt''
      | None -> ctxt''
    end
  (*    |> remove_var ~loc:(LLet e_id) remove_scope*)
  | Seq (e1, e2) ->
    let ctxt' = process_expr ctxt e1 in
    process_expr ?output_type ~remove_scope ctxt' e2
      
  | Assign (lhs,IVar rhs,cont) ->
    let (ctxt',(t1,t2)) = split_type ctxt @@ lkp rhs in
    let (_,o)  = lkp_ref lhs in
    let t2_eq = strengthen_eq ~strengthen_type:t2 ~target:(`AVar rhs) in
    let nxt = add_owner_con [Write o] ctxt'
      |> update_type rhs t1
      |> update_type lhs @@ ref_of t2_eq o
    in
    process_expr ?output_type ~remove_scope nxt cont
      
  | Assign (lhs,IInt i,cont) ->
    let (_,o) = lkp_ref lhs in
    let ctxt' =
      add_owner_con [Write o] ctxt
      |> update_type lhs @@ ref_of (Int (ConstEq i)) o
    in
    process_expr ?output_type ~remove_scope ctxt' cont
      
  | Let (patt,rhs,((cont_id,_) as exp)) ->
    let ctxt,assign_type = begin
      match rhs with
      | Var left_v ->
        let (ctxt',(t1,t2)) = split_type ctxt @@ lkp left_v in
        ctxt'
        |> update_type left_v t1
        |> with_type t2
      | Const n -> (ctxt,Int (ConstEq n))
      | Nondet -> (ctxt, Int Top)
      | Call c -> process_call ~e_id ~cont_id ctxt c
      | Deref ptr ->
        let (target_type,o) = lkp_ref ptr in
        let (ctxt',(t1,t2)) = split_type ctxt target_type in
        ctxt'
        |> update_type ptr @@ (ref_of t1 o)
        |> add_owner_con [Live o]
        |> with_type t2
      | Ast.Tuple tl ->
        let rec make_tuple c ind i_list =
          match i_list with
          | [] -> (c,[],[])
          | h::t ->
            let (ctxt',ty_rest,b_list) = make_tuple c (ind + 1) t in
            let (ctxt'',ty,flag) = 
            match h with
            | RNone -> (ctxt',Int Top,true)
            | RInt n -> (ctxt',Int (ConstEq n), true)
            | RVar v ->
              let (c_,(t1,t2)) = split_type ctxt' @@ lkp v in
              (update_type v t2 c_,t1, match t1 with Int _ -> true | _ -> false)
            in
            let b_list' = if flag then
                (fresh_tvar (), SProj ind)::b_list
              else b_list
            in
            (ctxt'',ty::ty_rest,b_list')
        in
        let (c',ty_list,t_binding) = make_tuple ctxt 0 tl in
        c',Tuple (t_binding,ty_list)
      | Mkref init' ->
        match init' with
        | RNone -> (ctxt,Ref (Int Top,OConst 1.0))
        | RInt n -> (ctxt, Ref (Int (ConstEq n),OConst 1.0))
        | RVar r_var ->
          let (ctxt',(t1,t2)) = split_type ctxt @@ lkp r_var in
          update_type r_var t1 ctxt'
          |> with_type @@ Ref (t2,OConst 1.0)
    end in
    let _,assign_ctxt,close_p = assign_patt ~let_id:e_id ctxt patt assign_type in
    let str_ctxt = strengthen_let close_p rhs assign_ctxt in
    let bound_vars = collect_bound_vars SS.empty close_p in
    process_expr ?output_type (*~remove_scope:(SS.union bound_vars remove_scope)*) str_ctxt exp
    |> remove_var ~loc:(LLet e_id) bound_vars
      
  | Assert (relation,cont) ->
    cont
    |> process_expr ?output_type ~remove_scope @@ add_constraint (denote_gamma ctxt.gamma) ctxt Top (lift_relation relation)

  | Alias (v1,ap2,((next_id,_) as cont)) ->
    let loc = LAlias e_id in
    (* get the variable type *)
    let t1 = lkp v1 |> meet_ownership e_id ctxt.o_info @@ (`AVar v1) in
    (* compute the free vars *)
    let free_vars = predicate_vars @@ SM.bindings ctxt.gamma in

    (* silly *)
    let ap = lift_src_ap ap2 in

    (* now make a fresh type for the location referred to by ap *)
    (* return back the context, substitution, free vars, and new type *)
    let ((ctxt',t2',ap_fv,subst),t2_base) = map_ap_with_bindings ap free_vars (fun (fv,subst) t ->
        (* here fv may refer to the _symbolic_ variables for tuple elements contained in the value
           stored in the root of ap2. The fresh type for v1 must also refer to these variables *)
        let (c_fresh,t2') = make_fresh_type ~target_var:ap ~loc ~fv ~bind:subst t ctxt in
        let t2'own = meet_ownership next_id ctxt.o_info ap t2' in
        ((c_fresh,t2'own,fv,subst),t2'own)
      ) lkp in
    (* extract the original t2 type *)
    let (t2,_) = map_ap_with_bindings ap free_vars (fun (_,subst') t ->
        assert (subst' = subst);
        (t |> meet_ownership e_id ctxt.o_info ap,t)
      ) lkp in
    let ap_fv_const = List.filter (function
      | #Paths.concr_ap as cr -> Paths.is_const_ap cr
      | `Sym i -> List.assoc i subst |> Paths.is_const_ap
      ) ap_fv
    in
    let force_v1_cons = List.length ap_fv_const <> List.length ap_fv in
    let (ctxt'',t1'sym) = make_fresh_type ~target_var:(`AVar v1) ~loc ~fv:ap_fv_const ~bind:subst t1 ctxt' in
    let t1'own = meet_ownership next_id ctxt.o_info (`AVar v1) t1'sym in
    (* now t1' is a fresh type with the same shape at t1, but with fresh predicates potentially 
       referring to (unbound!) symbolic variables. We now push the substitution for t2 into t1'sym *)
    let t1' = walk_with_bindings (fun _ _ r () ->
        ((), partial_subst subst r)
      ) (`AVar v1) ([],[]) t1'own () |> snd in
    (* now t1' and t2' refer to the same sets of free variables: any symbolic variables
       appearing in t1' and t2' are bound by tuple types *)
    let app_matrix = apply_matrix ~t1 ~t2_bind:subst ~t2 in
    (* function to update t2 *)
    let rec up_ap ap t2_base' ctxt = match ap with
      | `AVar v -> update_type v t2_base' ctxt
      | `ADeref ap
      | `AProj (ap,_) -> up_ap ap t2_base' ctxt
    in
    let (ctxt'app,(psub2,psub1)) =
      ctxt''
      |> (app_matrix ~force_cons:false ~out_root:ap ~out_bind:subst ~out_type:t2' >>
        app_matrix ~force_cons:force_v1_cons ~out_root:(`AVar v1) ~out_type:t1')
    in
    let res = ctxt'app
      |> shuffle_owners t1 t2 t1' t2'
      |> up_ap ap @@ sub_pdef psub2 t2_base
      |> update_type v1 @@ sub_pdef psub1 t1'
      |> remove_sub psub1
      |> remove_sub psub2
    in
    process_expr ?output_type ~remove_scope res cont

  | Cond(v,e1,e2) ->
    let add_pc_refinement ctxt cond =
      let curr_ref = lkp v in
      let branch_refinement = {
        rel_op1 = Nu;
        rel_cond = cond;
        rel_op2 = RConst 0
      } in
      ctxt |>
      update_type v @@ map_refinement (fun r -> And (r,Relation branch_refinement)) curr_ref
    in
    let ctxt1 = process_expr ?output_type ~remove_scope (add_pc_refinement ctxt "=") e1 in
    let ctxt2 = process_expr ?output_type ~remove_scope (add_pc_refinement {
        ctxt with
          refinements = ctxt1.refinements;
          v_counter = ctxt1.v_counter;
          ownership = ctxt1.ownership;
          pred_arity = ctxt1.pred_arity;
          ovars = ctxt1.ovars
        } "!=") e2 in
    let loc = LCond e_id in
    let u_ctxt = { ctxt2 with gamma = SM.empty } in
    let b1 = SM.bindings ctxt1.gamma in
    let b2 = SM.bindings ctxt2.gamma in
    let predicate_vars = predicate_vars @@ b1 in
    let dg1 = denote_gamma ctxt1.gamma in
    let dg2 = denote_gamma ctxt2.gamma in
    let subsume_types ctxt ~target_var t1 t2 =
      let (ctxt',t') = make_fresh_type ~loc ~target_var:(`AVar target_var) ~fv:predicate_vars t1 ctxt in
      let c_up =
        add_var_implication dg1 ctxt1.gamma target_var t' ctxt'
        |> add_var_implication dg2 ctxt2.gamma target_var t'
        |> constrain_owner t1 t'
        |> constrain_owner t2 t'
      in
      (c_up,t')
    in
    List.fold_left2 (fun ctxt (k1,t1) (k2,t2) ->
      assert (k1 = k2);
      let (ctxt',t) = subsume_types ctxt ~target_var:k1 t1 t2 in
      add_type k1 t ctxt'
    ) u_ctxt b1 b2

and make_fresh_type ~target_var ~loc ~fv ?(bind=[]) t ctxt =
  walk_with_bindings ~o_map:(fun c _ ->
    alloc_ovar c
  ) (fun p (sym_vars,sym_vals) _ context ->
    make_fresh_pred ~loc ~pred_vars:(sym_vars,p,sym_vals) context
  ) target_var (fv,bind) t ctxt
    
and process_call ~e_id ~cont_id ctxt c =
  let arg_bindings = List.mapi (fun i k ->
      (i,k,SM.find k ctxt.gamma)) c.arg_names
  in
  let p_vars = predicate_vars @@ List.map (fun (_,k,v) -> (k,v)) arg_bindings in
  let inst_symb path (fv,sym_vals) f_refinement () =
    ((),
     match f_refinement with
     | InfPred p -> 
       CtxtPred (c.label,p,filter_fv path sym_vals fv)
     | True -> Top
     | BuiltInPred f -> NamedPred (f,fv))
  in
  let inst_concr target_var (fv,subst) f_refinement () =
    let (_, symb_out) = inst_symb target_var (fv,subst) f_refinement () in
    ((), compile_refinement target_var subst symb_out)
  in
  let input_env = ctxt.gamma |> denote_gamma in
  let callee_type = SM.find c.callee ctxt.theta in
  let inst_fn_type f = List.map (fun (a,t) ->
      walk_with_bindings f (`AVar a) (p_vars,[]) t ()
      |> snd
    )
  in
  let concr_in_t = List.combine c.arg_names callee_type.arg_types
    |> inst_fn_type inst_concr in
  let symb_out_t = List.combine c.arg_names callee_type.output_types
    |> inst_fn_type inst_symb in
  let in_out_types = List.combine concr_in_t symb_out_t in
  (* TODO: consistently use this function *)
  let post_type_vars = gamma_predicate_vars ctxt.gamma in
  let loc = LCall c.label in
  let updated_ctxt = List.fold_left2 (fun acc (i,k,arg_t) (in_t,out_t) ->
      let constrain_in t c =
        let concr_arg_type = compile_type t k in
        add_type_implication input_env concr_arg_type in_t c
        |> constrain_owner t in_t
      in
      if post_update_type arg_t then
        let ap = `AVar k in
        (* split the argument type *)
        let arg_t_o = meet_ownership e_id acc.o_info ap arg_t in
        let (ctxt',(resid,formal)) = split_arg i c.callee acc arg_t_o in
        (* the (to be) summed type *)
        let (ctxt'',fresh_type) = make_fresh_type ~target_var:ap ~loc ~fv:post_type_vars arg_t ctxt' in
        let (ctxt''',psub) = apply_matrix
            ~t1:resid
            ~t2:(meet_out i c.callee ctxt'' out_t)
            ~force_cons:false
            ~out_root:ap
            ~out_type:(meet_ownership cont_id ctxt''.o_info ap fresh_type)
            ctxt'' in
        (* now the magic *)
        ctxt'''
        (* constrain the formal half of the arg type *) 
        |> constrain_in formal
        |> sum_ownership resid out_t fresh_type
        |> update_type k @@ sub_pdef psub fresh_type
        |> remove_sub psub
      else
        constrain_in arg_t acc
    ) ctxt arg_bindings in_out_types
  in
  let result = walk_with_bindings inst_symb (`AVar "dummy") (p_vars,[]) callee_type.result_type () |> snd in
  (updated_ctxt, result)

let process_function_bind ctxt fdef =
  let arg_names = fdef.args in
  let f_typ = SM.find fdef.name ctxt.theta in
  let typ_template = List.combine arg_names f_typ.arg_types in
  let fv = predicate_vars typ_template in
  let inst_symb n t =
    walk_with_bindings (fun path (fv,sym_vals) p () ->
      match p with
        | InfPred id -> (),Pred (id,filter_fv path sym_vals fv)
        | _ -> assert false
    ) (`AVar n) (fv,[]) t ()
    |> snd
  in
  let init_env = List.fold_left (fun g (n,t) ->
      let inst = inst_symb n t in
      SM.add n inst g
    ) SM.empty typ_template
  in
  let result_type = inst_symb "Ret" f_typ.result_type in
  let ctxt' = process_expr ~output_type:result_type ~remove_scope:SS.empty { ctxt with gamma = init_env } fdef.body in
  let out_typ_template = List.combine arg_names f_typ.output_types in
  let result_denote = ctxt'.gamma |> denote_gamma in
  List.fold_left (fun acc (v,out_ty) ->
      let out_refine_type = inst_symb v out_ty in
      add_var_implication result_denote acc.gamma v out_refine_type acc
      |> constrain_owner (SM.find v acc.gamma) out_refine_type
    ) ctxt' out_typ_template

let process_function ctxt fdef =
  let c = process_function_bind ctxt fdef in
  { c with gamma = SM.empty }

let print_pred_details t =
  Hashtbl.iter (fun k { fv; loc; target_var } ->
    Printf.fprintf stderr "%d: >>\n" k;
    Printf.fprintf stderr "  Free vars: [%s]\n" @@ String.concat ", " @@ List.map refine_ap_to_string fv;
    Printf.fprintf stderr "  Target var: %s\n" @@ refine_ap_to_string target_var;
    Printf.fprintf stderr "  At: %s\n<<\n" @@ loc_to_string loc
  ) t
  
let infer ~print_pred ~save_types ?o_solve ~intrinsics st (fns,main) =
  let init_fun_type ctxt f_def =
    let rec lift_simple_loop target_var ~loc (free_vars,sym) t ctxt =
      match t with
      | `Int ->
        let (ctxt',i) = alloc_pred ~loc  (free_vars,target_var,sym) ctxt in
        (ctxt',Int (InfPred i))
      | `Ref st' ->
        let (ctxt',o) = alloc_ovar ctxt in
        let (ctxt'',t') = lift_simple_loop (`ADeref target_var) ~loc (free_vars,sym) st' ctxt' in
        (ctxt'',Ref (t',o))
      | `Tuple stl ->
        let i_stl = List.mapi (fun i st -> (i,st)) stl in
        let b = List.filter (fun (_,t) -> t = `Int) i_stl
          |> List.map (fun (i,_) -> (fresh_tvar (),SProj i))
        in
        let binding' = update_binding target_var b (free_vars,sym) in
        let (ctxt',tl') = List.fold_right (fun (i,st) (c_acc,tl_acc) ->
            let (c_acc',te) = lift_simple_loop (`AProj (target_var,i)) ~loc binding' st c_acc in
            (c_acc',te::tl_acc)
          ) i_stl (ctxt,[]) in
        (ctxt',Tuple (b,tl'))
    in
    let lift_simple_type target_var ~loc fv t =
      lift_simple_loop (`AVar target_var) ~loc (fv,[]) t
    in
    let gen_arg_preds ~loc fv arg_templ ctxt = List.fold_right (fun (k,t) (acc_c,acc_ty) ->
        let (ctxt',t') = lift_simple_type k ~loc fv t acc_c in
        (ctxt',t'::acc_ty)
      ) arg_templ (ctxt,[])
    in
    let simple_ftype = SM.find f_def.name st in
    let arg_templ = List.combine f_def.args simple_ftype.SimpleTypes.arg_types in
    let free_vars = List.filter (fun (_,t) -> t = `Int) arg_templ |> List.map (fun (n,_) -> (`AVar n)) in
    let (ctxt',arg_types) = gen_arg_preds ~loc:(LArg f_def.name) free_vars arg_templ ctxt in
    let (ctxt'',output_types) = gen_arg_preds ~loc:(LOutput f_def.name) free_vars arg_templ ctxt' in
    let (ctxt''', result_type) =
      lift_simple_type "RET" ~loc:(LReturn f_def.name) free_vars simple_ftype.SimpleTypes.ret_type ctxt''
    in
    { ctxt''' with
      theta = SM.add f_def.name {
          arg_types; output_types; result_type
        } ctxt'''.theta
    }
  in
  let ty_envs = Hashtbl.create 10 in
  let store_env =
    if save_types then
      Hashtbl.add ty_envs
    else
      (fun _ _ -> ())
  in
  let initial_ctxt = {
    theta = intrinsics;
    gamma = SM.empty;
    ownership = [];
    ovars = [];
    refinements = [];
    pred_arity = IntMap.empty;
    v_counter = 0;
    pred_detail = Hashtbl.create 10;
    store_env;
    o_info = (match o_solve with
    | Some e -> e
    | None -> (Hashtbl.create 10,SM.empty))
  } in
  let ctxt = List.fold_left init_fun_type initial_ctxt fns in
  let ctxt' = List.fold_left process_function ctxt fns in
  let { pred_detail; refinements; ownership; ovars; pred_arity; theta; _ } = process_expr ctxt' main in
  if print_pred then print_pred_details pred_detail;
  Result.{
    ownership;
    ovars;
    refinements;
    theta;
    arity = pred_arity;
    ty_envs 
  }
  

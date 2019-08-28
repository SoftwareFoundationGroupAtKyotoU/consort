open Ast
open RefinementTypes
open Sexplib.Std
open Std
open Std.StateMonad
open SimpleChecker.SideAnalysis
    
module SM = StringMap
module SS = StringSet
module P = Paths

type concr_ap = P.concr_ap

type pred_loc =
  | LCond of int
  | LArg of string * string
  | LReturn of string
  | LOutput of string * string
  | LAlias of int
  | LLet of int
  | LCall of int * string
  | LRead of int
  | LUpdate of int
  | LNull of int
  | LMkArray of int
  | LFold of int

let loc_to_string =
  let labeled_expr s i = Printf.sprintf "%s@%d" s i in
  let fn_nm_loc = Printf.sprintf "fn %s %s %s" in
  let fn_loc = Printf.sprintf "fn %s %s" in
  function
  | LCond i -> labeled_expr "if" i
  | LArg (f,a) -> fn_nm_loc f "Arg" a
  | LReturn f -> fn_loc f "Ret"
  | LOutput (f,a) -> fn_nm_loc f "Out" a
  | LAlias i -> labeled_expr "alias" i
  | LLet i -> labeled_expr "let" i
  | LCall (i,a) -> labeled_expr a i
  | LNull i -> labeled_expr "ifnull" i
  | LFold i -> labeled_expr "fold" i
  | LRead i -> labeled_expr "read" i
  | LMkArray i -> labeled_expr "mkarray" i
  | LUpdate i -> labeled_expr "update" i

type pred_context = {
  fv: refine_ap list;
  loc: pred_loc;
  target_var: concr_ap
}

type funenv = funtype SM.t
type tenv = typ SM.t

type ownership_type = (unit, float,unit) RefinementTypes._typ
type o_theta = ownership_type RefinementTypes._funtype StringMap.t
type o_solution = ((int,ownership_type StringMap.t) Hashtbl.t * o_theta)
type type_hints = int -> (SimpleTypes.r_typ StringMap.t) option

type oante =
  | ORel of ownership * [ `Eq | `Ge | `Gt ] * float
  | OAny of oante list [@@deriving sexp]

let sexp_of_tenv = SM.sexp_of_t ~v:sexp_of_typ

type tcon = {
  env: (Paths.concr_ap * concr_refinement * nullity) list;
  ante: concr_refinement;
  conseq: concr_refinement;
  owner_ante: oante list;
  nullity: nullity
}[@@deriving sexp]

exception Incompleteness of string

type ocon =
  (* Constraint ownership variable n to be 1 *)
  | Write of ownership
  (* ownership has to be greater than 0 *)
  | Live of ownership
  (* ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Shuff of (ownership * ownership) * (ownership * ownership)
  | Split of ownership * (ownership * ownership)
  | Eq of ownership * ownership
  (* For well-formedness: if o1 = 0, then o2 = 0 *)
  | Wf of ownership * ownership [@@deriving sexp]


type context = {
  theta: funenv;
  gamma: tenv;
  ownership: ocon list;
  ovars: int list;
  refinements: tcon list;
  pred_arity: (bool * int) StringMap.t;
  v_counter: int;
  pred_detail: (int,pred_context) Hashtbl.t;
  store_env: int -> tenv -> unit;
  o_info: o_solution;
  type_hints: type_hints;
  iso: SimpleChecker.SideAnalysis.results
}

module Result = struct
  type t = {
    theta: funenv;
    ownership: ocon list;
    ovars: int list;
    refinements: tcon list;
    arity: (bool * int) StringMap.t;
    ty_envs: (int,tenv) Hashtbl.t
  }
end

let t_var_counter = ref 0;;

let fresh_tvar () =
  let v = !t_var_counter in
  incr t_var_counter;
  v

let type_mismatch t1 t2 =
  let tag1 = Obj.repr t1 |> Obj.tag in
  let tag2 = Obj.repr t2 |> Obj.tag in
  (assert (tag1 <> tag2); failwith "Mismatched types")

let alloc_ovar ctxt =
  ({ ctxt with v_counter = ctxt.v_counter + 1; ovars = ctxt.v_counter::ctxt.ovars }, OVar ctxt.v_counter)

let unsupported s = raise @@ Incompleteness s

let do_with f l = ignore (f l); l

let add_owner_con l ctxt = { ctxt with ownership = l @ ctxt.ownership  }

let alloc_split o =
  let%bind o1 = alloc_ovar in
  let%bind o2 = alloc_ovar in
  add_owner_con [ Split (o,(o1,o2)) ]
  >> return (o1,o2)

let constrain_well_formed t ctxt =
  let rec wf_loop last_o acc = function
    | TVar _
    | Int _ -> acc
    | Array (_,_,o,t)
    | Ref (t,o,_) ->
      let c_acc' = Option.fold ~some:(fun last ->
          add_owner_con [Wf (last,o)] acc
        ) ~none:acc last_o in
      wf_loop (Some o) c_acc' t
    | Tuple (_,tl) ->
      List.fold_left (wf_loop last_o) acc tl
    | Mu (_,_,_,t) -> wf_loop last_o acc t
  in
  wf_loop None ctxt t


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

let denote_array_vars ~nullity path bind len_r =
  let len_ap = (`ALen path) in
  let len_comp = compile_refinement len_ap bind len_r in
  let ind_ap = (`AInd path) in
  [
    (len_ap,len_comp,nullity);
    (ind_ap, NamedPred ("valid-ind", ([ len_ap ],ind_ap)), nullity)
  ]

let rec denote_type ?(nullity=`NLive) path (bind: (int * Paths.concr_ap) list) acc t =
  match t with
  | Array (b,len_r,_,et) ->
    let arr_b = bind_of_arr b path in
    let acc' = (denote_array_vars ~nullity path bind len_r) @ acc in
    denote_type ~nullity (`AElem path) (arr_b @ bind) acc' et
  | Ref (t',_,_) -> denote_type ~nullity:`NUnk (`ADeref path) bind acc t'
  | Int r ->
    let comp_r = compile_refinement path bind r in
    (path,comp_r,nullity)::acc
  | Tuple (b,t) ->
    let (bind' : (int * Paths.concr_ap) list) = (subst_of_binding path b) @ bind in
    List.mapi (fun i te -> (i,te)) t
    |> List.fold_left (fun acc (i,te) ->
        denote_type ~nullity (`AProj (path,i)) bind' acc te
      ) acc
  | TVar _ -> acc
  | Mu (_,_,_,t) -> denote_type ~nullity path bind acc t

let with_pred_refl root r =
  match root with
  | `ADeref _ -> r
  | _ -> And (r,Relation { rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp root })

let with_refl ap t =
  map_with_bindings (fun ~pos:{under_mu; _ } root _ r->
    if under_mu then
      r
    else
      with_pred_refl root r
  ) ap ([],[]) t

let denote_gamma gamma =
  SM.fold (fun v t acc ->
    denote_type (`AVar v) [] acc t
  ) gamma []

let denote_gamma_m ctxt = (ctxt,denote_gamma ctxt.gamma)

let rec split_ref_type (t,o,n) =
  let%bind (o1,o2) = alloc_split o in
  let%bind (t1,t2) = split_type t in
  let t1' = Ref (t1,o1,n) in
  let t2' = Ref (t2,o2,n) in
  return (t1', t2')
and split_type t =
  match t with
  | Int _ -> return (t,t)
  | Ref (t,o,n) ->
    split_ref_type (t,o,n)
  | Array (b,len_r,o,et) ->
    let%bind (et1,et2) = split_type et in
    let%bind (o1,o2) = alloc_split o in
    let t1 = Array (b,len_r,o1,et1) in
    let t2 = Array (b,len_r,o2,et2) in
    return (t1,t2)
  | Tuple (b,tl) ->
    let%bind (tl1,tl2) = mfold_right (fun t' (tl1,tl2) ->
        let%bind (t'1,t'2) = split_type t' in
        return (t'1::tl1,t'2::tl2)
      ) tl ([],[])
    in
    return (Tuple (b,tl1),Tuple (b,tl2))
  | TVar id -> return (TVar id,TVar id)
  | Mu (a,n,i,t) ->
    let%bind (t1,t2) = split_type t in
    return (Mu (a,n,i,t1), Mu (a,n,i,t2))

let rec unsafe_meet tr town =
  match tr,town with
  | Int r,Int _ -> Int r
  | Ref (r1,_,n), Ref (r2,o,_) ->
    Ref (unsafe_meet r1 r2,OConst o,n)
  | Tuple (b,tl1), Tuple (_,tl2) ->
    Tuple (b,List.map2 unsafe_meet tl1 tl2)
  | Mu (a,fv,i,t1), Mu (_,_,_,t2) ->
    Mu (a,fv,i,unsafe_meet t1 t2)
  | Array (b,len_r,_,et1), Array (_,_,o,et2) ->
    Array (b,len_r,OConst o,unsafe_meet et1 et2)
  | TVar t,TVar _ -> TVar t
  | _ -> type_mismatch tr town

let meet_arg i c_name ctxt in_t =
  let (_,o_th) = ctxt.o_info in
  if not @@ SM.mem c_name o_th then
    in_t
  else
    let { arg_types; _ } = SM.find c_name o_th in
    let o_in = List.nth arg_types i in
    unsafe_meet in_t o_in

let split_arg t1 t2 =
  let rec loop arg_t form_t =
    match arg_t,form_t with
    | Int r,Int _ -> return (Int r,Int r)
    | Ref (r1,OConst o,n), Ref (r2,OConst o_const,_) ->
      let%bind (t1,t2) = loop r1 r2 in
      let rem = o -. o_const in
      return (Ref (t1,OConst rem,n), Ref (t2,OConst o_const,n))
    | Ref (r1,o,n), Ref (r2,_,_) ->
      let%bind o1 = alloc_ovar in
      let%bind o2 = alloc_ovar in
      add_owner_con [ Split (o,(o1,o2)) ] >>
      let%bind (rn',rn'') = loop r1 r2 in
      return (Ref (rn',o1,n), Ref (rn'',o2,n))
    | Mu (a,n,i,t1), Mu (_,_,_,t2) ->
      let%bind (t1',t2') = loop t1 t2 in
      return (Mu (a,n,i,t1'), Mu (a,n,i,t2'))
    | Array (b,len_r,OConst o1,et_arg), Array (_,_,OConst o2,et_form) ->
      let%bind (et1',et2') = loop et_arg et_form in
      let rem = o1 -. o2 in
      return (Array (b,len_r,OConst rem,et1'), Array (b,len_r,OConst o2,et2'))
    | Array (b,len_r,o,et_arg), Array (_,_,_,et_form) ->
      let%bind (et1',et2') = loop et_arg et_form in
      let%bind (o1,o2) = alloc_split o in
      return (Array (b,len_r,o1,et1'),Array (b,len_r,o2,et2'))
    | TVar v,TVar _ -> return (TVar v, TVar v)
    | Tuple (b,tl1), Tuple (_,tl2) ->
      let%bind tl_split =
        map_with_accum (fun (a_t,f_t) ->
          loop a_t f_t
        ) @@ List.combine tl1 tl2
      in
      let (tl_s1,tl_s2) = List.split tl_split in
      return (Tuple (b,tl_s1), Tuple (b,tl_s2))
    | _ -> type_mismatch arg_t form_t
  in
  let%bind (t1'rem,t1'form) = loop t1 t2 in
  return_after (t1'rem,t1'form)
  <|> constrain_well_formed t1'rem
  <|> constrain_well_formed t1'form

let add_constraint gamma ?ante_ext ?(o=[]) ante conseq nullity ctxt =
  { ctxt with
    refinements = {
      env = gamma;
      ante = Option.fold ~some:(fun r -> And (r,ante)) ~none:ante ante_ext;
      conseq;
      owner_ante = o;
      nullity
    }::ctxt.refinements
  }

let constrain_owner t1 t2 =
  let rec loop t1 t2 ctxt =
    match t1,t2 with
    | Array (_,_,o1,r1), Array (_,_,o2,r2)
    | Ref (r1,o1,_),Ref (r2,o2,_) ->
      add_owner_con [Eq (o1,o2)] ctxt
      |> loop r1 r2
    | Int _,Int _ -> ctxt
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 (fun c te1 te2 ->
          loop te1 te2 c
        ) ctxt tl1 tl2
    | TVar _,TVar _ -> ctxt
    | Mu (_,_,_,t1'), Mu (_,_,_,t2') -> loop t1' t2' ctxt
    | _ -> type_mismatch t1 t2
  in
  loop t1 t2

let add_type_implication ?(filter_taut=false) ?ante_ext gamma t1_ t2_ ctxt_ =
  let rec impl_loop ~nullity ctxt t1 t2 =
    match t1,t2 with
    | Int r1, Int r2 ->
      if (not filter_taut) || r1 <> r2 || ante_ext <> None then
        add_constraint ?ante_ext gamma r1 r2 nullity ctxt
      else
        ctxt
    | Array (_,len_r1,_,et1), Array (_,len_r2,_,et2) ->
      let ctxt' = add_constraint ?ante_ext gamma len_r1 len_r2 nullity ctxt in
      impl_loop ~nullity ctxt' et1 et2
    | Ref (t1',_,_), Ref (t2',_,_) -> impl_loop ~nullity:`NUnk ctxt t1' t2'
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 (impl_loop ~nullity) ctxt tl1 tl2
    | TVar _,TVar _ -> ctxt
    | Mu (_,(),_,t1'), Mu (_,(),_,t2') ->
      impl_loop ~nullity ctxt t1' t2'
    | t1,t2 -> type_mismatch t1 t2
  in
  impl_loop ~nullity:`NLive ctxt_ t1_ t2_

let add_var_type_implication ?filter_taut dg var t1 t2 ctxt =
  let type_compile t = compile_type t var in
  let v_t =
    type_compile t1
    |> with_refl (`AVar var)
  in
  let to_t = type_compile t2 in
  add_type_implication ?filter_taut dg v_t to_t ctxt

let add_var_implication dg gamma var t ctxt =
  add_type_implication dg (compile_type (SM.find var gamma) var |> with_refl (`AVar var)) (compile_type t var) ctxt
  
let ext_names = true

let mk_pred_name ~mu n target_var loc =
  let c = 
    match loc with
    | LCond i -> Printf.sprintf "join-%d" i
    | LArg (f_name,a_name) -> Printf.sprintf "%s-%s-in" f_name a_name
    | LReturn f_name -> Printf.sprintf "%s-ret" f_name
    | LOutput (f_name, a_name) -> Printf.sprintf "%s-%s-out" f_name a_name
    | LAlias i -> Printf.sprintf "shuf-%d" i
    | LLet i -> Printf.sprintf "scope-%d" i
    | LCall (i,a) -> Printf.sprintf "call-%d-%s-out" i a
    | LNull i -> Printf.sprintf "ifnull-%d" i
    | LFold i -> Printf.sprintf "fold-%d" i
    | LRead i -> Printf.sprintf "read-%d" i
    | LUpdate i -> Printf.sprintf "update-%d" i
    | LMkArray i -> Printf.sprintf "mkarray-%d" i
  in
  if ext_names then
    c ^ "-" ^ (Paths.to_z3_ident target_var) ^ (if mu then "-mu" else "")
  else
    c ^ "-" ^ (string_of_int n)

let alloc_pred ~mu ~ground ~loc ?(add_post_var=false) fv target_var ctxt =
  let n = ctxt.v_counter in
  let arity = (List.length fv) +
      1 + !KCFA.cfa + (* 1 for nu and k for context *)
      (if add_post_var then 1 else 0) (* add an extra variable for post *)
  in
  let p_name = mk_pred_name ~mu n target_var loc in
  ({ ctxt with
     v_counter = n + 1;
     pred_arity = StringMap.add p_name (ground,arity) ctxt.pred_arity
   }, p_name)

let make_fresh_pred ~mu ~ground ~pred_vars:(fv,target) ~loc =
  let%bind p = alloc_pred ~mu ~ground ~loc fv target in
  return @@ Pred (p,fv)

let rec root_mu_path path = function
  | MRoot -> path
  | MProj (m_ap,i) -> `AProj (root_mu_path path m_ap, i)
  | MDeref m_ap -> `ADeref (root_mu_path path m_ap)
  | MElem m_ap -> `AElem (root_mu_path path m_ap)
  | MLen m_ap -> `ALen (root_mu_path path m_ap)

let mu_bind_update_cb =
  let apply_bind_set path {fv_map; pred_symbols}  (ctxt,(bind_set,_)) =
    let ps' = List.map (fun (m_ap,r) ->
        let c_ap = root_mu_path path m_ap in
        let new_r = Paths.PathMap.find_opt c_ap bind_set in
        match r,new_r with
        | Some _, Some _
        | None, _ -> (m_ap,new_r)
        | Some _, None -> (m_ap, None)
      ) pred_symbols in
    (ctxt,(Paths.PathMap.empty,Paths.PathMap.empty)),{fv_map; pred_symbols = ps' }
  in
  let generate_fv_map root _ {fv_map; _} (ctxt,(_,_)) =
    let fv_manager = List.fold_left (fun acc (mu_ap,ll) -> 
        Paths.PathMap.add (root_mu_path root mu_ap) ll acc
      ) Paths.PathMap.empty fv_map
    in
    (ctxt,(Paths.PathMap.empty,fv_manager)),()
  in
  generate_fv_map,apply_bind_set

let initial_walk_state = (Paths.PathMap.empty,Paths.PathMap.empty)

let plift f (ctxt,(ps,fv)) =
  let (ctxt',res) = f ctxt in
  (ctxt',(ps,fv)),res

type inference_refinement = (refine_ap list,refine_ap) refinement;;
type extra_context = (inference_refinement Paths.PathMap.t) * (int list * int list) Paths.PathMap.t

(* we very much assume fv does not contain (directly or through sym_map) path *)
let generate_refinement =
  let get_path_set = Fun.id in
  let return_with_path p r ctxt =
    ((ctxt,p),r)
  in
  fun ~ground ~loc ~pos (fv,_) path ->
    (* easy or hard *)
    if not pos.under_mu then
      let%bind path_set = get_path_set in
      let%bind r' = make_fresh_pred ~mu:false ~ground ~loc ~pred_vars:(fv,path) in
      return_with_path path_set r'
    else
      
      (* let's generate a recursive refinement. 

         A recursive refinement has two parts: the local refinement (LR),
         and the inductive refinement (IR). We'll call the tuple
         names bound by the tuple containing the mu binder OV and those
         inside the mu IV. We will call the variables in scope that are
         in neither set FV.

         Then the local refinement is a predicate over IV U FV. The inductive
         refinement is over IV U OV. The total refinement, called R, is
         the conjunction of these two predicates.

         When unfolding a type such that
         a fresh set of IV names called IV' are generated, we give the new
         refinement under the mu as: R[IV -> IV'] /\ IR[OV -> IV, IV -> IV']
         for a position with refinement R = IR /\ LR.

         And now on with the show.

         But WAIT! THERE'S MORE!

         How do we know what OV, IV, and FV are? This is where the "path set"
         comes into play (which needs to be renamed). When walking a type
         for generation, provides a map fv_manager which maps a concrete
         ap to the sets of ov and iv. This set is actually stored in
         the mu binders as map from mu_aps (or relative APs if you prefer)
         to these sets.

         But wait! How do we know when unfolding what the IV is? That's where
         the other component of the extra context comes into play, the (real)
         path set (WHICH REALLY NEEDS TO BE RENAMED!)
         
         If a new inductive invariant is generated, it is expected that the generated
         invariant is stored into the path set. After completely walking a recursive
         type, the mu_update_bind_cb will extract these predicates, map them BACK
         to relative paths, and then merge the results with the current binder list.
         (This "incremental" approach is necessitated by remove_var, which can piecewise
         replace components of types).

         All of the above complexity is handled by the mu_bind_update_cb which should be
         passed into the walk_with_bindings_own as the mu_map argument.
      *)
      let%bind (path_set,fv_manager) : extra_context = get_path_set in
      (* This will crash if the free variables haven't been bound for us *)
      let (ov_list,iv_list) = Paths.PathMap.find path fv_manager in
      let ov_set = IntSet.of_list ov_list in
      let iv_set = IntSet.of_list iv_list in
      let mu_vars = IntSet.union iv_set ov_set in
      let local_pred_fv = List.filter (function
        | `Sym i -> not (IntSet.mem i ov_set)
        | _ -> true) fv
      in
      (* inductive pred free variables *)
      let ind_pred_fv = List.filter (function
        | `Sym i -> IntSet.mem i mu_vars
        | _ -> false) fv
      in
      let%bind ind_pred = make_fresh_pred ~ground:true ~mu:true ~pred_vars:(ind_pred_fv,path) ~loc in
      let%bind local_pred = make_fresh_pred ~ground:true ~mu:false ~pred_vars:(local_pred_fv,path) ~loc in
      return_with_path (Paths.PathMap.add path local_pred path_set,fv_manager) (And (ind_pred,local_pred))

let generate_type ~ground ~target ~loc ~fv_seed ?(bind=[]) ~fv_gen t context =
  let ((ctxt,_),t') =
    walk_with_bindings_own ~o_map:(fun _ -> plift alloc_ovar) ~mu_map:mu_bind_update_cb
      (fun ~pos root (fv,bind) r ->
        let fv_add = fv_gen root fv r in
        generate_refinement ~loc ~ground ~pos (fv_add,bind) root
      ) target (fv_seed,bind) t (context,initial_walk_state)
  in
  (ctxt,t')

let make_fresh_type ?(ground=false) ~target_var ~loc ~fv ?(bind=[]) t =  
  let%bind fresh =
    generate_type ~ground ~target:target_var ~loc ~fv_seed:fv ~bind ~fv_gen:(fun _ fv _ ->
      fv
    ) t
  in
  return_after fresh <|> constrain_well_formed fresh

let rec free_vars_contains (r: concr_refinement) v_set =
  let root_pred ap = Paths.has_root_p (fun root -> SS.mem root v_set) ap in
  let imm_is_var ri = match ri with RConst _ -> false | RAp ap -> root_pred ap in
  match r with
  | Pred (_,(pv,_))
  | NamedPred (_,(pv,_))
  | CtxtPred (_,_,(pv,_)) -> List.exists root_pred pv
  | Relation { rel_op1 = op1; rel_op2 = op2; _ } ->
    imm_is_var op2 || (match op1 with
      RImm v -> imm_is_var v | Nu -> false)
  | And (r1, r2) -> free_vars_contains r1 v_set || free_vars_contains r2 v_set
  | _ -> false

let dump_env ?(msg) tev =
  (match msg with
  | Some m -> print_endline m;
  | None -> ());
  sexp_of_tenv tev |> Sexplib.Sexp.to_string_hum |> print_endline;
  flush stdout
[@@ocaml.warning "-32"] 

let predicate_vars kv =
  List.fold_left (fun acc (k, t) ->
      match t with
      | Int _ -> (`AVar k)::acc
      | _ -> acc
  ) [] kv |> List.rev

let gamma_predicate_vars gamma =
  SM.bindings gamma |> predicate_vars

let predicate_vars_m = mwith @@ (fun ctxt -> 
    SM.bindings ctxt.gamma |> predicate_vars)

let with_type t ctxt = (ctxt,t)

let map_tuple f b tl =
  Tuple (b,List.map f tl)

let map_ref f t o n =
  Ref (f t, o,n)

let rec unfold_once_gen unfolder = function
  | Int r -> Int r
  | Array (b,len_p,o,t) ->
    Array (b,len_p,o,unfold_once_gen unfolder t)
  | Ref (r, o,n) -> map_ref (unfold_once_gen unfolder) r o n
  | Tuple (b,tl) ->
    map_tuple (unfold_once_gen unfolder) b tl
  | Mu (a,fv,i,t) -> unfolder a fv i t
  | TVar _ -> assert false


let unfold_once = unfold_once_gen (unfold ~gen:fresh_tvar)

(* 
Generates a refinement type from a simple type.

This is nightmarishly complicated, but briefly, it works as follows.
* We generate a skeleton with no refinements, and just tuple positions (lift_to_skeleton)
* We then unfold any recursive types exactly once, generating for the
  unfolded mu type:
  - a substitution map, describing how tuple positions in the (now outer type) are mapped to their corresponding inner type positions
  - a scope map, describing what inner vars/outer vars are in scope at each mu positions
  - an application map, describing what predicates generated in the outer type should be pushed into the inner type
  This is implemented by unfold_once, push_subst, and do_subst

* We then walk the type, generating the actual predicates. Under the mu, we restrict the free variables to those computed in the previous step. The predicates here are then stored as the inductive predicates for the mu binder. This is implemented by the first call to walk_with_bindings_own
* We finally push the outer type refinements into the inner types, substituting as appropriate. This is implemented with the second call to walk_with_bindings_own
*)
(* TODO: explain this more, because I will not remember how it works in 2 minutes *)
let lift_to_refinement ~pred initial_path fv t =
  let rec lift_to_skeleton t =
    match t with
    | `Int -> Int ()
    | `Ref t' -> Ref (lift_to_skeleton t', (), `NUnk)
    | `Tuple stl ->
      let i_stl = List.mapi (fun i st -> (i,st)) stl in
      let b = List.filter (fun (_,t) -> t = `Int) i_stl
        |> List.map (fun (i,_) -> (fresh_tvar (),SProj i))
      in
      Tuple (b,List.map lift_to_skeleton stl)
    | `Mu (id,t) ->
      Mu ([],(),id,lift_to_skeleton t)
    | `TVar id -> TVar id
    | `Array et ->
      let ind_var = fresh_tvar () in
      let len_var = fresh_tvar () in
      let b = {len = len_var; ind = ind_var } in
      Array (b,(),(),lift_to_skeleton (et :> SimpleTypes.r_typ))
  in

  let do_subst outer_scope t =
    let put_scope mu_ap inner_scope (sub_map,app_map,scope_map) =
      (sub_map,app_map,(mu_ap,(outer_scope,inner_scope))::scope_map),()
    in
    let put_sub sub (sub_map,app_map,scope_map) =
      (sub::sub_map,app_map,scope_map),()
    in
    let rec loop mu_ap local_scope = function
      | TVar id -> return @@ TVar id
      | Mu (_,_,_,_) -> raise @@ Incompleteness "Nested recursive types"
      | Int () ->
        let%bind () = put_scope mu_ap local_scope in
        return @@ Int ()
      | Tuple (b,tl) ->
        let%bind b' = mmap (fun (k,v) ->
            let k' = fresh_tvar () in
            let%bind () = put_sub (k,k') in
            return @@ (k',v)
          ) b in
        let%bind tl' = mmapi (fun i t_e ->
            let local_scope' = local_scope @ List.filter_map (fun (k,p) ->
                  match p with
                  | SProj j when i = j -> None
                  | _ -> Some k
                ) b'
            in
            loop (MProj (mu_ap, i)) local_scope' t_e
          ) tl
        in
        return @@ Tuple (b',tl')
      | Array (_,(),(),t) ->
        let%bind () = put_scope (MLen mu_ap) local_scope in
        let ind_v = fresh_tvar () in
        let len_v = fresh_tvar () in
        let%bind t' = loop (MElem mu_ap) (local_scope @ [ ind_v; len_v ]) t in
        return @@ Array ({len = len_v; ind = ind_v},(),(),t')
      | Ref (t,(),n) ->
        let%bind t' = loop (MDeref mu_ap) local_scope t in
        return @@ Ref (t',(),n)
    in
    loop MRoot [] t
  in
  let put_app (abs,mu) app_map = (Paths.PathMap.add abs mu app_map,()) in
  let rec push_subst mu_type (abs_path,mu_path) in_scope (t: (unit, unit, unit) RefinementTypes._typ) =
    match t with
    | TVar id ->
      let%bind () = mutate (fun st -> ([],st,[])) in
      let%bind unfolded = do_subst in_scope mu_type in
      let%bind (sub_map,st',scope_map) = get_state in
      let%bind () = put_state st' in
      return @@ Mu (sub_map,scope_map,id,unfolded)
    | Mu (_,_,_,_) -> raise @@ Incompleteness "NESTED! TYPES!"
    | Ref (t,(),n) ->
      let%bind t' = push_subst mu_type (`ADeref abs_path, MDeref mu_path) in_scope t in
      return @@ Ref (t',(),n)
    | Int () ->
      let%bind () = put_app (abs_path,mu_path) in
      return @@ Int ()
    | Array (b,(),(),t) ->
      let%bind () = put_app (`ALen abs_path,MLen mu_path) in
      let%bind t' = push_subst mu_type (`AElem abs_path, MElem mu_path) (in_scope @ [b.ind;b.len]) t in
      return @@ Array (b,(),(),t')
    | Tuple (b,tl) ->
      let in_scope' = in_scope @ (List.map fst b) in
      let%bind tl' = mmapi (fun i t_e ->
          push_subst mu_type (`AProj (abs_path,i), MProj (mu_path,i)) in_scope' t_e
        ) tl
      in
      return @@ Tuple (b,tl')
  in
  
  let rec unfold_once path =
    function
    | Int () ->
      return @@ Int ()
    | TVar _ ->
      assert false
    | Mu (l,(),_,t) ->
      assert (l = []);
      push_subst t (path,MRoot) [] t
    | Array (a,b,c,t) ->
      let%bind t' = unfold_once (`AElem path) t in
      return @@ Array (a,b,c,t')
    | Tuple (b,tl) ->
      let%bind tl' = mmapi (fun i te ->
          unfold_once (`AProj (path,i)) te
        ) tl
      in
      return @@ Tuple (b,tl')
    | Ref (t,(),n) ->
      let%bind t' = unfold_once (`ADeref path) t in
      return @@ Ref (t',(),n)
  in

  let%bind ctxt = get_state in
  let%bind () = put_state Paths.PathMap.empty in
  let skeleton = lift_to_skeleton t in
  let%bind unfolded = unfold_once initial_path skeleton in
  let%bind app_map = get_state in
  let%bind () = put_state (ctxt,None,None) in

  let pre_mu path _ fv_list =
    let%bind (ctxt,fv_map_emp,bound_map_emp) = get_state in
    assert (fv_map_emp = None);
    assert (bound_map_emp = None);
    let fv_map = List.fold_left (fun acc (mu_ap,fv) ->
        Paths.PathMap.add (root_mu_path path mu_ap) fv acc
      ) Paths.PathMap.empty fv_list
    in
    put_state (ctxt,Some fv_map,Some Paths.PathMap.empty)
  in
  let post_mu path fv_list =
    let%bind (ctxt,_,bound_map_opt) = get_state in
    let bound_map = Option.get bound_map_opt in
    let pred_symbols = List.map (fun (mu_ap,_) ->
        (mu_ap,Paths.PathMap.find_opt (root_mu_path path mu_ap) bound_map)
      ) fv_list
    in
    let%bind () = put_state (ctxt,None,None) in
    return @@ { pred_symbols; fv_map = fv_list }
  in
  
  let mu_map = pre_mu,post_mu in
  
  let%bind t_inst = walk_with_bindings_own ~o_map:(fun () (ctxt,f,p) ->
      let (ctxt',o) = alloc_ovar ctxt in
      (ctxt',f,p),o
    ) ~mu_map (fun ~pos root (fv_loc,_) () ->
      if pos.under_mu then
        let%bind (ctxt,fv_map,bound_map) = get_state in
        let (ol,il) = Option.map (fun m ->
            Paths.PathMap.find root m
          ) fv_map
          |> Option.get
        in
        let rec_fv = IntSet.union (IntSet.of_list ol) (IntSet.of_list il) in
        let fv_act = List.filter (function
          | `Sym i -> IntSet.mem i rec_fv
          | _ -> false
          ) fv_loc
        in
        let (ctxt',r) = pred ~mu:true ~pos fv_act root ctxt in
        let bound_map' = Option.map (fun m ->
            Paths.PathMap.add root r m
          ) bound_map in
        let%bind () = put_state (ctxt',fv_map,bound_map') in
        return r
      else
        let%bind (ctxt,fv_map,bound_map) = get_state in
        let (ctxt',r) = pred ~mu:false ~pos fv_loc root ctxt in
        let%bind () = put_state (ctxt',fv_map,bound_map) in
        return r
    ) initial_path (fv,[]) unfolded
  in
  
  let%bind (ctxt',_,_) = get_state in
  let apply_preds = fold_with_bindings (fun ~pos p _ r acc ->
      if Paths.PathMap.mem p app_map then
        let app_pred =
          if pos.array <> [] then
            `ArrayPred (pos.array,r)
          else
            `Pred r
        in
        (Paths.PathMap.find p app_map,app_pred)::acc
      else
        acc
    ) initial_path ([],[]) t_inst []
  in
  (* now walk the type one final time, pushing the local refinements 
     into the leaves *)
  let setup_push path bind _ =
    let subst_map = (List.map (fun (k,i) -> (k,`Sym i)) bind) in
    let subst = function
      | `ArrayPred (al,r) -> `ArrayPred(al,partial_subst subst_map r)
      | `Pred r -> `Pred (partial_subst subst_map r)
    in
    let new_state = List.fold_left (fun acc (mu_ap,r) ->
        Paths.PathMap.add (root_mu_path path mu_ap) (subst r) acc
      ) Paths.PathMap.empty apply_preds
    in
    let%bind _ = get_state in
    put_state new_state
  in
  let post_push _ fv = return fv in    
  let (_,applied) =
    walk_with_bindings_own ~o_map:(fun c -> return c)
      ~mu_map:(setup_push,post_push) (fun ~pos root _ r ->
      let%swith to_conjoin = Paths.PathMap.find_opt root in
      let some_comb = function
        | `Pred r' -> And (r,r')
        | `ArrayPred (al,r') ->
          assert ((List.length al) = (List.length pos.array));
          let subst_map = List.map2 (fun i j ->
              [(i.len,`Sym j.len);
               (i.ind,`Sym j.ind)]
            ) al pos.array |> List.concat
          in
          And (r,partial_subst subst_map r')
      in
      return @@ Option.fold ~none:r ~some:some_comb to_conjoin
    ) initial_path ([],[]) t_inst Paths.PathMap.empty
  in
  let ctxt'' = constrain_well_formed applied ctxt' in
  let%bind () = put_state ctxt'' in
  return applied

let lift_src_ap = function
  | AVar v -> `AVar v
  | ADeref v -> `ADeref (`AVar v)
  | AProj (v,i) -> `AProj (`AVar v,i)
  | APtrProj (v,i) -> `AProj (`ADeref (`AVar v), i)


let get_ref_aps_gen proj =
  fold_refinement_args
    ~rel_arg:(fun l ap -> ap::l)
    ~pred_arg:(fun l ap -> proj ap @ l) []
   
let get_ref_aps = get_ref_aps_gen fst

(* t2 is the type to be copied w.r.t mu, tuple binding, etc. *)
let merge_types ~loc ~path ?(fv_filter=(fun _ -> true)) ?(e1_expl=[]) ?(bind_seed=([],[])) ?(unfold_t1=false) ?(unfold_t2=false) ~t1 ~t2 ctxt =
  let filter_expl em = List.filter_map (function
    | `Sym i -> if List.mem_assoc i em then
        Some (List.assoc i em)
      else None
    | #Paths.concr_ap as c -> Some c)
  in
  let counter = ref 0 in
  let gen_ref expl r =
    let fv_set = get_ref_aps_gen Fun.id r |> filter_expl expl |> List.filter fv_filter |> Paths.PathSet.of_list in
    let id = !counter in
    incr counter;
    (id,fv_set)
  in
  let rec to_type_template expl = function
    | Int r ->
      Int (gen_ref expl r)
    | Ref (r,_,n) ->
      Ref (to_type_template expl r, (), n)
    | Mu (a,{pred_symbols;fv_map},i,t) -> Mu (a,{
                                                pred_symbols = List.map (fun (a,_) -> (a,None)) pred_symbols; fv_map},i,to_type_template expl t)
    | TVar id -> TVar id
    | Tuple (b,tl) ->
      let expl' = List.fold_left (fun acc (i,p) ->
          match p with
          | SProj _ -> acc
          | SVar v -> (i,`AVar v)::acc
        ) expl b in
      Tuple (b,List.map (to_type_template expl') tl)
    | Array (b,l,_,t) ->
      Array (b,gen_ref expl l,(),to_type_template expl t)
      
  in
  let t1_fv_templ = to_type_template e1_expl t1 in
  let t2_fv_templ = to_type_template [] t2 in
  let merge_fvs (_,r1) (id,r2) map =
    IntMap.update id (fun bind ->
      Option.value ~default:(Paths.PathSet.empty) bind
      |> Paths.PathSet.union @@ Paths.PathSet.union r1 r2
      |> Option.some) map
  in
  let rec merge_loop t1_templ t2_templ map =
    match t1_templ, t2_templ with
    | Int r1,Int r2 -> merge_fvs r1 r2 map
    | Mu (_,_,_,t1), Mu (_,_,_,t2)
    | Ref (t1,_,_), Ref (t2,_,_) -> merge_loop t1 t2 map
    | Array (_,l1,_,t1), Array (_,l2,_,t2) ->
      merge_loop t1 t2 @@ merge_fvs l1 l2 map
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 (fun acc t1 t2 ->
          merge_loop t1 t2 acc
        ) map tl1 tl2
    | TVar _,TVar _ -> map
    | _,_ -> type_mismatch t1_templ t2_templ
  in
  let maybe_unfold f t =
    if f then
      unfold_once_gen (unfold_gen ~gen:fresh_tvar ~apply_ref:(fun r _ -> r) ~rmap:(fun _ r -> r)) t
    else
      t
  in
  let merge_map =
    merge_loop
      (maybe_unfold unfold_t1 t1_fv_templ)
      (maybe_unfold unfold_t2 t2_fv_templ)
      IntMap.empty
  in
  let (fv_seed,bind) = bind_seed in
  generate_type ~ground:false ~target:path ~loc ~fv_seed ~bind ~fv_gen:(fun _ sym_fv (id,_) ->
    ((Paths.PathSet.elements @@ (IntMap.find id merge_map)) :> refine_ap list) @ sym_fv
  ) t2_fv_templ ctxt

let remove_var_from_pred ~loc ~mk_fv ~oracle ~pos ~gamma path (sym_vars,sym_val) r =
  let curr_comp = compile_refinement path sym_val r in
  if oracle curr_comp path then
    let fv : refine_ap list = (mk_fv path curr_comp sym_vars sym_val) in
    let%bind new_pred = generate_refinement ~ground:false ~loc ~pos (fv,sym_val) path in
    let new_comp = compile_refinement path sym_val new_pred in
    let%bind (ctxt,p) = get_state in
    let%bind () = put_state @@ ((add_constraint gamma (curr_comp |> with_pred_refl path) new_comp `NUnk ctxt), p) in
    return new_pred
  else
    return r

let remove_var_from_type ~loc ~curr_te ~oracle ~mk_fv root_var t context =
  let staged = remove_var_from_pred ~gamma:curr_te ~mk_fv ~loc ~oracle in
  let ((ctxt',_),t') = walk_with_bindings_own ~mu_map:mu_bind_update_cb ~o_map:(fun c -> return c) staged root_var ([],[]) t (context,initial_walk_state) in
  (ctxt',t')

let rec purge_tuple_fv to_remove = function
  | Tuple (b,tl) ->
    let tl' = List.map (purge_tuple_fv to_remove) tl in
    let b' = List.filter (fun (_,p) ->
        match p with
        | SVar v -> not (SS.mem v to_remove)
        | _ -> true
      ) b in
    Tuple (b',tl')
  | Ref (t,o,n) -> Ref (purge_tuple_fv to_remove t,o,n)
  | Int r -> Int r
  | TVar id -> TVar id
  | Mu (n,i,a,t) -> Mu (n,i,a,purge_tuple_fv to_remove t)
  | Array (a,len_r,o,t) ->
    Array (a,len_r,o,purge_tuple_fv to_remove t)
    
let remove_var ~loc to_remove ctxt =
  let curr_te = denote_gamma ctxt.gamma in
  let module StrUF = UnionFind.Make(UnionFind.MakeHashed(struct
        type t = Paths.concr_ap
        let equal = (=)
      end)) in
  let eq_ref = StrUF.mk () in
  let has_remove_root = Paths.has_root_p @@ Fun.flip SS.mem @@ to_remove in
  let by_ref,ref_vars = SS.fold (fun var (by_var,all_ref) ->
      let ref_in = fold_with_bindings (fun ~pos:_ root (_,sym_vals) r a ->
          compile_refinement root sym_vals r
          |> get_ref_aps
          |> List.filter @@ Fun.negate has_remove_root
          (* this is very important because it implies that any free variables not
             rooted in predicate being removed can be safely referred to in the
             refinements of other predicates *)
          |> do_with @@ List.iter (fun l ->
                if not (Paths.is_const_ap l) then
                  failwith @@ Printf.sprintf "Invariant broken: %s %s (%s)"
                      (Paths.to_z3_ident l)
                      (Paths.to_z3_ident root)
                      (PrettyPrint.pretty_print_gen_rev pp_ref r)
                else ()
              )
          |> do_with @@ List.iter @@ StrUF.register eq_ref
          |> do_with @@ Std.fold_left_fst (fun a ->
                do_with @@ StrUF.union eq_ref a)
          |> List.fold_left (Fun.flip Paths.PathSet.add) a
        ) (`AVar var) ([],[]) (SM.find var ctxt.gamma) Paths.PathSet.empty
      in
      (SM.add var ref_in by_var, Paths.PathSet.union all_ref ref_in)
    ) to_remove (StringMap.empty,Paths.PathSet.empty)
  in
  let add_vars = Paths.PathSet.fold (fun p ->
      let key = StrUF.find eq_ref p in
      Paths.PathMap.update
        key (fun v -> Option.some @@ Option.fold
            ~none:(Paths.PathSet.singleton p)
            ~some:(Paths.PathSet.add p) v)
    ) ref_vars Paths.PathMap.empty
  in
  let removal_oracle = (fun r path ->
    (Paths.PathSet.mem path ref_vars) || (free_vars_contains r to_remove)
  ) in
  let free_var_manager root_var path curr_ref sym_vars sym_subst =
    let outer_var_p = Fun.negate @@ Paths.has_root root_var in
    let sym_vars_filtered = List.filter (function
      | `Sym i ->
        let concr = List.assoc i sym_subst in
        not (has_remove_root concr)
      | _ -> assert false
      ) sym_vars in
    let all_free_vars = get_ref_aps curr_ref in
    (* The free variables of THIS refinement,
       NOT bound by dependent tuples, and
       NOT rooted in to remove variables *)
    let curr_live_free_vars =
      List.filter (fun p ->
        (not @@ has_remove_root p) && outer_var_p p
      ) all_free_vars
      |> Paths.PathSet.of_list
    in
    (* Retrieve the set of paths in the same
       refinement equivalence as v *)
    let get_var_group v =
      StrUF.maybe_find eq_ref v
      |> Fun.flip Paths.PathMap.find_opt @@ add_vars
      |> Option.value ~default:Paths.PathSet.empty
    in
    (* The set of variables collectively referenced by the removed
       variables referenced by THIS assignment *)
    let induced_by_ref : Paths.PathSet.t =
      all_free_vars
      |> List.filter has_remove_root
      (* the roots of all variables to remove *)
      |> List.map Paths.unsafe_get_root
      (* (Optional) sets of paths referenced in all refinements in that root *)
      |> List.map @@ (Fun.flip SM.find_opt) by_ref
      (* Fold over these sets, accumulating them with the current live vars *)
      |> List.fold_left (fun path_set ref_by_removed_o ->
          match ref_by_removed_o with
          | None -> path_set
          (* This is a set of referenced variables, inner fold *)
          | Some ref_by_removed ->
            Paths.PathSet.fold (fun v acc' ->
                Paths.PathSet.union acc' @@ get_var_group v
              ) ref_by_removed path_set
        ) curr_live_free_vars
    in
    (* Now get the variables in THIS refinements, refinement equivalence, merge
       with the above as necessary, and return *)
    let concr_args =
      get_var_group path
      |> Paths.PathSet.union induced_by_ref
      |> Paths.PathSet.elements
      (* "defensive" programming *)
      |> List.filter outer_var_p |> List.map (fun l -> (l :> refine_ap))
    in
    concr_args @ sym_vars_filtered
  in
  let remove_fn = remove_var_from_type ~loc ~curr_te ~oracle:removal_oracle in
  let updated =
    SM.fold (fun v_name t c ->
      if SS.mem v_name to_remove then
        c
      else
        let (c',t') = remove_fn ~mk_fv:(free_var_manager v_name) (`AVar v_name) t c in
        let t_purge = purge_tuple_fv to_remove t' in
        { c' with gamma = SM.add v_name t_purge c'.gamma }
    ) ctxt.gamma { ctxt with gamma = SM.empty }
  in
  updated

let lift_imm_op_to_rel = function
  | IVar v -> RAp ((`AVar v) :> concr_ap)
  | IInt n -> RConst n

let lift_relation { rop1; cond; rop2 } =
  Relation { rel_op1 = RImm (lift_imm_op_to_rel rop1); rel_cond = cond; rel_op2 = lift_imm_op_to_rel rop2 }

(* Strengthen the type strengthen_type to be equal to target t *)
(* at the moment, this ONLY propagates equalities along constant paths,
   namely bare variables, tuple elements, and array lengths (i.e., 
   we do not strengthen under refs *)
let rec strengthen_eq ~strengthen_type ~target =
  match strengthen_type with
  | Int r ->
    let r' = And (r,Relation {
          rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (target :> refine_ap)
        })
    in
    Int r'
  | Array (b,l,o,t) ->
    let l' = And (l, Relation {
           rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp ((`ALen target) :> refine_ap)
        })
    in
    Array (b,l',o,t)
  | Ref _ -> strengthen_type
  | Tuple (b,tl) ->
    let tl' = List.mapi (fun i t ->
        strengthen_eq ~strengthen_type:t ~target:(Paths.t_ind target i)
      ) tl in
    Tuple (b,tl')
  | Mu _ -> strengthen_type
  | TVar _ -> failwith "Top level unfolded type!!!"

type walk_ctxt = {
  o_stack: ownership list;
  binding: (int * concr_ap) list;
  env: (Paths.concr_ap * concr_refinement * nullity) list;
  path: concr_ap;
}

let step_tup wc b tl =
  let binding = (subst_of_binding wc.path b) @ wc.binding in
  let env = fold_lefti (fun ind e t ->
      match t with
      | Int _ -> denote_type ~nullity:`NUnk (`AProj (wc.path,ind)) binding e t
      | _ -> e
    ) wc.env tl
  in
  fun i t ->
    ({ wc with
       path = `AProj (wc.path,i);
       binding;
       env;
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

let unsafe_split_ref = function
  | Ref (r,o,n) -> r,o,n
  | _ -> failwith "You were supposed to give me a ref :("

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
  let rec gen_ap_loop ?(arr_ap=(fun _ -> failwith "Invalid nesting of access paths")) ap ~exc ~k =
    if ap = root then
      k (root :> refine_ap) out_type
    else
      let pass_through = (fun ~pre _ -> exc ~pre (ap :> refine_ap)) in
      match ap with
      | `APre v -> exc ~pre:true (`APre v)
      | `AVar v -> exc ~pre:false (`AVar v)
      | `AFree _ -> failwith "Impossible but here we are anyway :("
      | `ADeref ap' ->
        gen_ap_loop ap'
          ~exc:(fun ~pre _ ->
            if pre then
              exc ~pre (ap :> refine_ap)
            else
              failwith @@ "Free deref rooted outside target " ^ (string_of_type out_type) ^ " " ^ P.to_z3_ident root
          )
          ~k:(fun _ t ->
            match t with
            | Ref (t',_,_) -> k (ap :> refine_ap) t'
            | _ -> assert false)
      | `ALen ap' ->
        gen_ap_loop ap' ~exc:pass_through
          ~k:(fun _ t ->
            match t with
            | Array ({len; _},_,_,_) -> arr_ap @@ `Sym len
            | _ -> assert false
          )
      | `AInd ap' ->
        gen_ap_loop ap' ~exc:pass_through
          ~k:(fun _ t ->
            match t with
            | Array ({ind; _},_,_,_) -> arr_ap @@ `Sym ind
            | _ -> assert false
          )
      | `AElem ap' ->
        gen_ap_loop ap' ~exc:(fun ~pre _ ->
            assert (not pre);
            failwith @@ "Free array element rooted outside target " ^ (string_of_type out_type) ^ " " ^ P.to_z3_ident root
          ) ~k:(fun _ t ->
            match t with
            | Array (_,_,_,t') ->
              k (ap :> refine_ap) t'
            | _ -> assert false
          )
      | `AProj (ap',i) -> 
        gen_ap_loop ap'
          ~exc:(fun ~pre _ -> exc ~pre (ap :> refine_ap))
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
  let gen_ap ap = gen_ap_loop ~arr_ap:(fun ap -> ap) ap ~exc:(fun ~pre:_ t -> t) ~k:(fun ap _ -> ap)in
  let rec gen_loop = function
    | Top -> Top
    | ConstEq n -> ConstEq n
    | And (r1,r2) -> And (gen_loop r1,gen_loop r2)
    | Relation r -> Relation (RefinementTypes.map_relation gen_ap r)
    | Pred (i,(fv,_)) -> Pred (i,List.map gen_ap fv)
    | CtxtPred (i1,i2,(fv,_)) -> CtxtPred (i1,i2,List.map gen_ap fv)
    | NamedPred (nm,(fv,_)) -> NamedPred (nm,List.map gen_ap fv)
  in
  gen_loop combined_pred

let step_array wc b o len_ref t =
  {
    path = `AElem wc.path;
    o_stack = o::wc.o_stack;
    binding = (bind_of_arr b wc.path) @ wc.binding;
    env = (denote_array_vars ~nullity:`NUnk wc.path wc.binding len_ref) @ wc.env 
  },t

(* apply_matrix walks t1, t2 and out_type in parallel. At each leaf
   node, it generates a constrain on out_type's refinements based
   on the ownerships along the paths from the roots of t1 and t2 to the leaf.
*)
let apply_matrix ?pp_constr ~t1 ?(t2_bind=[]) ~t2 ?(force_cons=true) ~out_root ?(out_bind=[]) ~out_type ctxt =
  let (g,filtered_scope) = denote_gamma ctxt.gamma
    |> List.partition (fun (p,_,_) ->
        not (Paths.has_prefix out_root p)
      )
  in
  let const_filtered = List.filter (fun (p,_,_) -> Paths.is_const_ap p) filtered_scope in
  let pp = match pp_constr with
    | None -> (fun ~summary:_ _ p -> p)
    | Some f -> f in

  let shuffle_refinements ~env ~summary (c1,r1) (c2,r2) (c_out,out_r) ctxt =
    let gen_constraint =
      (force_cons) ||
      (not @@ List.for_all all_const_o [c1; c2; c_out]) ||
      summary || true
    in
    let c_out_r = ctxt_compile_ref c_out out_r in
    let c_r1 = ctxt_compile_ref c1 r1 in
    let c_r2 = ctxt_compile_ref c2 r2 in
    let close_env e =
      let bound_ap = List.fold_left (fun ap_set (p,_,_) ->
          Paths.PathSet.add p ap_set
        ) Paths.PathSet.empty e
      in
      List.fold_left (fun e_acc ((p,_,_) as bind) ->
        if not (Paths.PathSet.mem p bound_ap) then
          bind::e_acc
        else
          e_acc
      ) e const_filtered
    in
    let add_env c = close_env @@ env @ c.env in
    let join_envs c1 c2 =
      assert (List.length c1.env = List.length c2.env);
      let e1 = List.fast_sort (fun (p1,_,_) (p2,_,_) ->
          Paths.compare p1 p2
        ) c1.env
      in
      let e2 = List.fast_sort (fun (p1,_,_) (p2,_,_) ->
          Paths.compare p1 p2
        ) c2.env
      in
      close_env @@ List.fold_left2 (fun acc (p1,r1,_) (p2,r2,_) ->
        assert (p1 = p2);
        (p1,And (r1,r2),`NUnk)::acc
      ) env e1 e2
    in
    if gen_constraint then
      let mk_constraint env oante ante =
        pp ~summary c1.path @@ {
          env;
          ante;
          conseq = c_out_r;
          owner_ante = (ctxt_gt c_out) @ oante;
          nullity = `NUnk
        }
      in
      let cons = [
        mk_constraint (join_envs c1 c2) ((ctxt_gt c1) @ (ctxt_gt c2)) @@ And (c_r1,c_r2);
        mk_constraint (add_env c2) ((ctxt_any_eq c1) @ (ctxt_gt c2)) @@ c_r2;
        mk_constraint (add_env c1) ((ctxt_gt c1) @ (ctxt_any_eq c2)) @@ c_r1;
        pp ~summary c1.path @@ {
          env = close_env @@ env @ (List.map (fun (p,_,n) -> (p,Top,n)) c1.env);
          ante = Top;
          conseq = c_out_r;
          owner_ante = ctxt_any_eq c_out;
          nullity = `NUnk
        }
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
  in

  (* TODO: remove the ~env arg, it is pointless *)
  let rec inner_loop ~env ~summary (c1,t1) (c2,t2) (c_out,out_t) ctxt =
    match t1,t2,out_t with
    | Tuple (b1,tl1), Tuple (b2,tl2), Tuple (b_out,tl_out) ->
      let st1 = step_tup c1 b1 tl1 in
      let st2 = step_tup c2 b2 tl2 in
      let st3 = step_tup c_out b_out tl_out  in
      fold_left3i (fun c ind t1' t2' t_out' ->
        inner_loop ~env ~summary
          (st1 ind t1')
          (st2 ind t2')
          (st3 ind t_out')
          c
      ) ctxt tl1 tl2 tl_out
        
    | Ref (t1',o1,_), Ref (t2',o2,_), Ref (t_out',o_out,_) ->
      inner_loop ~env ~summary
        (step_ref c1 o1 t1')
        (step_ref c2 o2 t2')
        (step_ref c_out o_out t_out')
        ctxt
        
    | TVar _,TVar _,TVar _ ->
      ctxt
        
    | Mu (_,_,_,t1'), Mu (_,_,_,t2'), Mu (_,_,_,out_t') ->
      inner_loop ~env ~summary:true (c1,t1') (c2,t2') (c_out,out_t') ctxt
        
    | Int r1,Int r2,Int out_r ->
      shuffle_refinements ~env ~summary
        (c1,r1)
        (c2,r2)
        (c_out,out_r)
        ctxt
        
    | Array (b1,len1,o1,t1), Array (b2,len2,o2,t2), Array (b_out,len_out,o_out,t_out) ->
      let ctxt' = shuffle_refinements ~env ~summary:true (c1,len1) (c2,len2) (c_out,len_out) ctxt in
      inner_loop ~env ~summary:true
        (step_array c1 b1 o1 len1 t1)
        (step_array c2 b2 o2 len2 t2)
        (step_array c_out b_out o_out len_out t_out)
        ctxt'
        
    | _ -> failwith @@ Printf.sprintf "Mismatched types %s + %s = %s"
          (string_of_type t1)
          (string_of_type t2)
          (string_of_type out_t)
  in
  let mk_ctxt b t =
    ({
      path = out_root;
      binding = b;
      o_stack = [];
      env = [];
    },t)
  in
  inner_loop ~env:g ~summary:false
    (mk_ctxt [] t1)
    (mk_ctxt t2_bind t2)
    (mk_ctxt out_bind out_type)
    (ctxt,[])

let rec push_subst bind = function
  | Int r ->
    let sigma = List.map (fun (i,v) -> (i,`AVar v)) bind in
    Int (partial_subst sigma r)
  | Ref (t,o,n) -> map_ref (push_subst bind) t o n
  | Tuple (b,tl) ->
    let b_ext = List.map (fun (i,v) -> (i,SVar v)) bind in
    Tuple (b_ext @ b, tl)
  | TVar id -> TVar id
  | Mu (i,fv,a,t) -> Mu (i,fv,a,push_subst bind t)
  | Array (b,len_p,o,t) ->
    let sigma = List.map (fun (i,v) -> (i,`AVar v)) bind in
    let len_p' = partial_subst sigma len_p in
    Array (b,len_p',o,push_subst bind t)

let sub_pdef : (string * (refine_ap list, refine_ap) refinement) list -> (typ -> typ) =
  function
  | [] -> Fun.id
  | sub_assoc ->
    map_refinement (function
      | (Pred (i,_) as r) -> List.assoc_opt i sub_assoc |> Option.value ~default:r
      | r -> r)

let rec assign_patt ~let_id p t =
  let gen_var (id,ctxt) =
    (id+1,ctxt),id
  in
  match p,t with
  | PNone, _ -> return p
  | p,Mu (a,fv,i,t') ->
    assign_patt ~let_id p @@ unfold ~gen:fresh_tvar a fv i t'
  | PVar v,_ -> (fun (count,ctxt) -> (count,add_type v t ctxt),p)
  | PTuple t_patt,Tuple (b,tl) ->
    let%bind closed_patt = mfold_right2 (fun p t p_acc ->
        match p,t with
        | PNone, Int _ ->
          let%bind fresh_id = gen_var in
          let t_name = Printf.sprintf "__t_%d_%d" let_id fresh_id in
          return @@ (PVar t_name)::p_acc
        | _ -> return @@ p::p_acc
      ) t_patt tl []
    in
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
    let%bind t_patt' = mfold_left2 (fun patt_acc sub_p sub_t ->
        let%bind p = assign_patt ~let_id sub_p @@ push_subst var_subst sub_t in
        return @@ p::patt_acc
      ) [] closed_patt tl in
    return @@ PTuple (List.rev t_patt')
  | _,TVar _ -> failwith "Attempt to assign raw tvar to variable"
  | PTuple _,_ -> failwith @@ "Attempt to deconstruct value of non-tuple type: " ^ (string_of_type t)

let rec collect_bound_vars acc patt =
  match patt with
  | PVar v -> SS.add v acc
  | PTuple pl -> List.fold_left collect_bound_vars acc pl
  | PNone -> acc

(* t is the type of the location on the RHS that is being bound (and destructed
   by assignment to patt.
   Root is the access path name being assign FROM *)
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
  | Array _,PVar v ->
    maybe_strengthen_patt v ctxt
    (* strengthen eq, as a special case, can propagate length equalites *)
    |> with_type @@ strengthen_eq ~strengthen_type:t ~target:(`AVar v)
  | Array _,_ ->
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
        let sub_root = Option.map (fun r -> Paths.t_ind r i) root in
        let (c_acc',t') = strengthen_type ?root:sub_root t p ctxt_acc in
        (c_acc', t'::tl_acc)
      ) ind_tl pl (ctxt,[]) in
    (ctxt', Tuple (b,tl'))
  | (TVar _ | Mu _),_ -> (ctxt,t)
  | _ -> assert false

let rec strengthen_let patt rhs ctxt =
  let lkp_ref v = match SM.find v ctxt.gamma with
    | Ref (r,o,n) -> (r,o,n)
    | _ -> failwith "not a ref"
  in
  let lkp_array v = match SM.find v ctxt.gamma with
    | Array (b,l,o,et) -> (b,l,o,et)
    | _ -> failwith "not an array"
  in
  match patt,rhs with
  | PNone,_ -> ctxt
  | _,Const _
  | _,Mkref RNone
  | _,Mkref (RInt _)
  | _,Nondet
  | _,Null
  | _,Call _ -> ctxt
  | _,Var v ->
    let t = SM.find v ctxt.gamma in
    let (ctxt',t') = strengthen_type ~root:(`AVar v) t patt ctxt in
    update_type v t' ctxt'
  (* In the future, _maybe_ we want to explore strengthening equalities
     with array contents. I suspect it will just wreck z3 *)
  | _,Read _ -> ctxt

  (* Note that we can automatically strengthen the length equality
     when we generate the type for mkarray v, because that strengthening
     is entirely within the type of the array
     
     TODO: actually move to here for consistency sake *)
  | _,MkArray _ -> ctxt

  | PVar lhs,LengthOf arr ->
   let t' = strengthen_eq ~strengthen_type:(SM.find lhs ctxt.gamma) ~target:(`ALen (`AVar arr)) in
   let (b,l,o,et) = lkp_array arr in
   ctxt
   |> update_type lhs t'
   |> update_type arr @@ Array (b,And (l,Relation {
             rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`AVar lhs)
           }),o,et)
  | _,Deref v ->
    let (t,o,n) = lkp_ref v in
    let (ctxt',t') = strengthen_type t patt ctxt in
    update_type v (Ref (t',o,n)) ctxt'
  | (PVar v),Mkref (RVar v') ->
    let (t,o,n) = lkp_ref v in
    let t' = strengthen_eq ~strengthen_type:t ~target:(`AVar v') in
    update_type v (Ref (t',o,n)) ctxt
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
  | _ -> failwith "Ill-typed pattern (simple checker broken?)"


let shuffle_owners t1 t2 t1' t2' =
  let rec loop t1 t2 t1' t2' ctxt =
    match t1,t2,t1',t2' with
    | Int _,Int _,Int _,Int _ -> ctxt
    | Ref (r1,o1,_),Ref (r2,o2,_), Ref (r1',o1',_), Ref(r2',o2',_) ->
      loop r1 r2 r1' r2' @@
        { ctxt with
          ownership = Shuff ((o1,o2),(o1',o2')) :: ctxt.ownership }
    | Tuple (_,tl1), Tuple (_,tl2), Tuple (_,tl1'), Tuple (_,tl2') ->
      let orig_tl = List.combine tl1 tl2 in
      let new_tl = List.combine tl1' tl2' in
      List.fold_left2 (fun ctxt' (te1,te2) (te1',te2') ->
        loop te1 te2 te1' te2' ctxt'
      ) ctxt orig_tl new_tl
    | Mu (_,_,_,m1), Mu (_,_,_,m2), Mu (_,_,_,m1'), Mu (_,_,_,m2') ->
      loop m1 m2 m1' m2' ctxt
    | TVar _, TVar _, TVar _, TVar _ -> ctxt
    | _ -> failwith "Type mismatch (simple checker broken?)"
  in
  loop t1 t2 t1' t2'

let rec post_update_type = function
  | Int _ -> false
  | Tuple (_,tl) -> List.exists post_update_type tl
  | Array _
  | Ref _ -> true
  | TVar _ | Mu _ -> failwith "Bare recursive type"

let sum_ownership t1 t2 out ctxt =
  let rec loop t1 t2 out ctxt =
    match t1,t2,out with
    | Int _, Int _, Int _ -> ctxt
    | Ref (r1,o1,_), Ref (r2,o2,_), Ref (ro,oo,_) ->
      loop r1 r2 ro
        { ctxt with ownership = (Split (oo,(o1,o2)))::ctxt.ownership}
    | Tuple (_,tl1), Tuple (_,tl2), Tuple (_,tl_out) ->
      fold_left3i (fun ctxt _ e1 e2 e_out ->
          loop e1 e2 e_out ctxt) ctxt tl1 tl2 tl_out
    | Mu (_,_,_,t1'), Mu (_,_,_,t2'), Mu (_,_,_,out') ->
      loop t1' t2' out' ctxt
    | TVar _,TVar _, TVar _ -> ctxt
    | Array (_,_,o1,et1), Array (_,_,o2,et2), Array (_,_,o3,et3) ->
      loop et1 et2 et3
        { ctxt with ownership = Split (o3,(o1,o2))::ctxt.ownership }
    | _ -> failwith "Mismatched types (simple checker broken?)"
  in
  loop t1 t2 out ctxt

let remove_sub ps ctxt =
  List.fold_left (fun c (i,_) ->
    { c with pred_arity =
        StringMap.remove i c.pred_arity }) ctxt ps

let meet_loop t_ref t_own =
  let rec loop t_ref t_own =
    match t_ref,t_own with
    | Int r,Int () -> Int r
                        
    | Ref (t_ref',_,n),Ref (t_own',o,_) ->
      Ref (loop t_ref' t_own', OConst o,n)

    | Array (b,l,_,t_ref'), Array (_,_,o,t_own') ->
      Array (b,l,OConst o,loop t_ref' t_own')
    | Tuple (b,tl_ref), Tuple (_,tl_own) ->
      let tl_ref_cons = List.map2 loop tl_ref tl_own in
      Tuple (b,tl_ref_cons)
    | Mu (i,fv,a,t1), Mu (_,_,_,t2) ->
      Mu (i,fv,a,loop t1 t2)
    | TVar v,TVar _ -> TVar v
    | _ -> type_mismatch t_ref t_own
  in
  loop t_ref t_own

let add_post_type_p pos path =
  (not pos.under_mu) && (not pos.array_ref) && not @@ Paths.is_const_ap path

let meet_ownership st_id ap t { o_info = (o_envs,_); _ } =
  Hashtbl.find_opt o_envs st_id
  |> Option.map (fun o_env -> 
      map_ap ap (fun o_typ ->
        meet_loop t o_typ) (fun s -> SM.find s o_env)
    )
  |> Option.value ~default:t

let meet_gamma st_id g ctxt =
  SM.mapi (fun v t ->
    meet_ownership st_id (`AVar v) t ctxt) g

let meet_out i callee t ctxt =
  let (_,o_th) = ctxt.o_info in
  SM.find_opt callee o_th
  |> Option.map (fun { output_types; _ } ->
      unsafe_meet t @@ List.nth output_types i
    )
  |> Option.value ~default:t

let constrain_fold  ~unfolded:(unfolded_t,unfolded_v) ~folded:(folded_t,_) ctxt =
  let folded_unfold = unfold_once folded_t in
  let folded_c = compile_type_path folded_unfold (`AVar unfolded_v) in
  ctxt
  |> add_type_implication (denote_gamma ctxt.gamma) (compile_type unfolded_t unfolded_v) folded_c
  |> constrain_owner unfolded_t folded_unfold

let simple_type_at id v ctxt = 
  ctxt.type_hints id
  |> Fun.flip Option.bind @@ StringMap.find_opt v
  |> Option.get

let get_type_scheme ?(is_null=false) ~loc ~fv id v =
  let%swith st = simple_type_at id v in
  lift_to_refinement ~pred:(fun ~mu ~pos:{under_mu; _} fv p ->
      let%bind p = alloc_pred ~mu ~ground:(under_mu || is_null) ~loc fv p in
      return @@ Pred (p,fv)
  ) (`AVar v) fv st

let bind_var v t ctxt =
  { ctxt with gamma = SM.add v t ctxt.gamma }

let add_bounds_constraint dg arr_var ind_var ctxt =
  let len_ap = RAp (`ALen (`AVar arr_var)) in
  let index_constr = And (Relation {
        rel_op1 = Nu; rel_cond = ">="; rel_op2 = RConst 0
      }, Relation {
        rel_op1 = Nu; rel_cond = "<"; rel_op2 = len_ap
      })
  in
  add_var_implication dg ctxt.gamma ind_var (Int index_constr) ctxt

let rec process_expr ?output_args ?output_type ?(remove_scope=SS.empty) (e_id,e) ctxt =
  
  let lkp v = SM.find v ctxt.gamma in
  let lkp_ref v = match lkp v with
    | Ref (r,o,n) -> (r,o,n)
    | _ -> failwith "Not actually a ref"
  in
  let lkp_array v = match SM.find v ctxt.gamma with
    | Array (b,l,o,et) -> (b,l,o,et)
    | _ -> failwith "not an array"
  in
  let maybe_unfold ({ iso = { unfold_locs; _ }; _ } as ctxt) t =
    if IntSet.mem e_id unfold_locs then
      ctxt,(unfold_once t)
    else
      ctxt,t
  in
  let ctxt = { ctxt with
    gamma = meet_gamma e_id ctxt.gamma ctxt;
  } in
  ctxt.store_env e_id @@ ctxt.gamma;

  match e with
  | EVar v ->
    do_with_context ctxt @@
      let%bind (t1,t2) = split_type @@ lkp v in
      let%bind () = mutate @@ update_type v t1 in
      let%bind () = begin
        let c_type t = compile_type t "<ret>" in
        match output_type with
        | Some t ->
          let%bind d = denote_gamma_m in
          let dg = denote_type (`AVar "<ret>") [] d t2 in
          return_mut
          <|> add_type_implication dg (c_type t2 |> with_refl (`AVar v)) (c_type t)
          <|> constrain_owner t2 t
        | None -> return_mut
      end in
      let%bind () = begin
        match output_args with
        | None -> return_mut
        | Some out_args ->
          let%swith gamma = (fun ctxt -> ctxt.gamma) in
          let dg' = denote_gamma gamma in
          let%bind () = miter (fun (k,ty) ->
              return_mut
              <|> add_var_implication dg' gamma k ty
              <|> constrain_owner (SM.find k gamma) ty
            ) out_args in
          print_endline "done";
          return_mut
      end in
      let%bind () = mutate @@ remove_var ~loc:(LLet e_id) remove_scope in
      return_mut
  | Seq (e1, e2) ->
    process_expr e1 ctxt
    |> process_expr ?output_args ?output_type ~remove_scope e2

  | Assign (lhs,IVar rhs,cont) ->
    do_with_context ctxt @@
      let%bind (t1,t2) = split_type @@ lkp rhs in
      let (orig,o,_)  = lkp_ref lhs in
      let%bind t2_assign =
        if IntSet.mem e_id ctxt.iso.fold_locs then
          let%bind t2_fresh = make_fresh_type ~target_var:(`ADeref (`AVar lhs)) ~fv:(gamma_predicate_vars ctxt.gamma) ~loc:(LFold e_id) orig in
          
          constrain_fold ~folded:(t2_fresh,`ADeref (`AVar lhs)) ~unfolded:(t2,rhs)
          >> return t2_fresh
        else
          return t2
      in
      let t2_eq = strengthen_eq ~strengthen_type:t2_assign ~target:(`AVar rhs) in
      return_mut
      <|> add_owner_con [Write o]
      <|> update_type rhs t1
      <|> update_type lhs @@ ref_of t2_eq o `NLive
      <|> process_expr ?output_args ?output_type ~remove_scope cont

  | Assign (lhs,IInt i,cont) ->
    let (_,o,_) = lkp_ref lhs in
    add_owner_con [Write o] ctxt
    |> update_type lhs @@ ref_of (Int (ConstEq i)) o `NLive
    |> process_expr ?output_args ?output_type ~remove_scope cont

  | Update (base,ind,v,cont) ->
    let (b,l,o,et) = lkp_array base in
    (* we are being a little sloppy by happily assuming that len and index are in scope *)
    (* they are by virtue of denote gamma, but we REALLY need to do better with our
       generation of free variables *)
    let elem_ap = `AElem (`AVar base) in
    let arr_vars = bind_of_arr b (`AVar base) in
    
    do_with_context ctxt @@
      let%bind et' = make_fresh_type ~target_var:elem_ap ~loc:(LUpdate e_id) ~fv:(gamma_predicate_vars ctxt.gamma @ fv_of_arr b) ~bind:(arr_vars) et in
      let%bind (t1,t2) = split_type @@ lkp v in
      let%bind dg = denote_gamma_m in
      let c_up = compile_type t1 v |> with_refl (`AVar v) in
      let orig_cont = compile_type_gen et elem_ap arr_vars in
      let new_cont_up = compile_type_gen et' (`AVar v) arr_vars in
      let new_cont_same = compile_type_gen et' elem_ap arr_vars in
      let symb_ind_ap = RImm (RAp (`AInd (`AVar base))) in
      let ind_ap = RAp (`AVar ind) in

      return_mut
      <|> add_type_implication ~ante_ext:(Relation { rel_op1 = symb_ind_ap; rel_cond = "="; rel_op2 = ind_ap }) dg c_up new_cont_up
      <|> add_type_implication ~ante_ext:(Relation { rel_op1 = symb_ind_ap; rel_cond = "!="; rel_op2 = ind_ap }) dg orig_cont new_cont_same
      <|> add_owner_con [Write o]
      <|> add_bounds_constraint dg base ind
      <|> update_type v t2
      <|> update_type base @@ Array (b,l,o,et')
      <|> process_expr ?output_args ?output_type ~remove_scope cont

  | Let (PVar v,Mkref (RVar v_ref),((cont_id,_) as exp)) when IntSet.mem e_id ctxt.iso.fold_locs ->
    (* FOLD, EVERYBODY FOLD *)
    do_with_context ctxt @@
      let%bind fv = predicate_vars_m in
      let%bind fresh_type = get_type_scheme ~loc:(LFold e_id) ~fv cont_id v in
      let (fresh_cont,o,_) = unsafe_split_ref fresh_type in
      let fresh_strengthened = strengthen_eq ~strengthen_type:fresh_cont ~target:(`AVar v_ref) in
      let%bind (t1,t2) = split_type @@ lkp v_ref in
      return_mut
      <|> constrain_fold ~folded:(fresh_cont,(`ADeref (`AVar v))) ~unfolded:(t2,v_ref)
      <|> update_type v_ref t1
      <|> bind_var v @@ ref_of fresh_strengthened o `NLive
      <|> add_owner_con [Write o]
      <|> process_expr ?output_args ?output_type ~remove_scope:(SS.add v remove_scope) exp

  | Let (patt,rhs,((cont_id,_) as exp)) ->
    do_with_context ctxt @@
    let%bind assign_type = begin
      match rhs with
      | Var left_v ->
        let%bind (t1,t2) = split_type @@ lkp left_v in
        return_after t2 <|> update_type left_v t1
            
      | Const n -> return @@ Int (ConstEq n)
        
      | Nondet -> return @@ Int Top
        
      | Call c -> process_call ~e_id ~cont_id @> c
                    
      | Null -> begin
        match patt with
        | PNone -> return @@ Int Top
        | PTuple _ -> assert false
        | PVar v -> get_type_scheme ~is_null:true ~fv:(gamma_predicate_vars ctxt.gamma) ~loc:(LNull e_id) cont_id v
        end
      | Deref ptr ->
        let (target_type,o,_) = lkp_ref ptr in
        let%bind (t1,t2) = split_type @@ target_type in
        let%bind t2_unfold = maybe_unfold @> t2 in
        return_after t2_unfold
        <|> update_type ptr @@ (ref_of t1 o `NLive)
        <|> add_owner_con [Live o]

      | Ast.Tuple tl ->
        let rec make_tuple ind i_list =
          match i_list with
          | [] -> return ([],[])
          | h::t ->
            let%bind (ty_rest,b_list) = make_tuple (ind + 1) t in
            let%bind (ty,flag) = 
              match h with
              | RNone -> return (Int Top,true)
              | RInt n -> return (Int (ConstEq n), true)
              | RVar v ->
                let%bind (t1,t2) = split_type @@ lkp v in
                update_type v t2
                >> return (t1, match t1 with Int _ -> true | _ -> false)
            in
            let b_list' = if flag then
                (fresh_tvar (), SProj ind)::b_list
              else b_list
            in
            return (ty::ty_rest,b_list')
        in
        let%bind ty_list,t_binding = make_tuple 0 tl in
        return (Tuple (t_binding,ty_list))

      | Read (base,ind) ->
        let%bind dg = denote_gamma_m in
        let (b,_,o,et) = lkp_array base in
        let%bind fv = predicate_vars_m in
        (* TODO: no splitting because, uh, what would that look like? *)
        let%bind res_t = make_fresh_type ~loc:(LRead e_id) ~target_var:(`AElem (`AVar base)) ~fv et in
        let comp_res_t = compile_type_path res_t (`AElem (`AVar base)) in
        let comp_cont = compile_type_gen et (`AElem (`AVar base)) [ (b.ind, (`AVar ind)); (b.len,(`ALen (`AVar base))) ] in
        return_after res_t
        <|> add_type_implication dg comp_cont comp_res_t
        <|> add_bounds_constraint dg base ind
        <|> add_owner_con [ Live o ]

      | LengthOf _ ->
        return @@ Int (Relation {rel_op1 = Nu; rel_cond = ">="; rel_op2 = RConst 0 })
      | MkArray len ->
        begin
          match patt with
          | PTuple _ -> assert false
          | PNone -> raise @@ Incompleteness "Stahp"
          | PVar lhs ->
            let%bind dg = denote_gamma_m
            and fv = predicate_vars_m in
            let%swith st = simple_type_at cont_id lhs in
            let%bind a_type =
              lift_to_refinement ~pred:(fun ~mu ~pos:{under_ref; under_mu; _} fv path c ->
                  match path with
                  | `ALen (`AVar v) when v = lhs ->
                    (c,Relation { rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`AVar len) })
                  | `ALen _ -> unsupported "Nested arrays"
                  | _ -> if under_ref || under_mu then
                      make_fresh_pred ~mu ~ground:true ~pred_vars:(fv,path) ~loc:(LMkArray e_id) c
                    else
                      c,ConstEq 0
              ) (`AVar lhs) fv st
            in
            (match a_type with
            | Array (_,_,o,_) ->
              add_owner_con [Eq (o,OConst 1.0)]
            | _ -> assert false)
            >> add_var_implication dg ctxt.gamma len @@ Int (Relation { rel_op1 = Nu; rel_cond = ">="; rel_op2 = RConst 0 })
            >> update_type len (map_refinement (fun r ->
                And (r,Relation {rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`ALen (`AVar lhs)) })
              ) @@ lkp len)
            >> return a_type
        end

      | Mkref init' ->
        match init' with
        | RNone -> return @@ Ref (Int Top,OConst 1.0,`NLive)
        | RInt n -> return @@ Ref (Int (ConstEq n),OConst 1.0,`NLive)
        | RVar r_var ->
          let%bind (t1,t2) = split_type @@ lkp r_var in
          return_after (Ref (t2,OConst 1.0,`NLive)) <|> update_type r_var t1
    end in
    map_state (fun x -> (0,x)) >>
    let%bind close_p = assign_patt ~let_id:e_id patt assign_type in
    let bound_vars = collect_bound_vars SS.empty close_p in
    map_state snd >>
    return_mut
    <|> strengthen_let close_p rhs
    <|> process_expr ?output_args ?output_type ~remove_scope:(SS.union bound_vars remove_scope) exp

  | Assert (relation,cont) ->
    process_expr ?output_args ?output_type ~remove_scope cont @@ add_constraint (denote_gamma ctxt.gamma) Top (lift_relation relation) `NUnk ctxt

  | Alias (v1,src_ap,((next_id,_) as cont)) ->
    
    let loc = LAlias e_id in
    (* get the variable type *)
    let t1 = ctxt |> meet_ownership e_id (`AVar v1) @@ lkp v1 in
    (* silly *)
    let ap = lift_src_ap src_ap in
    (* Why are we checking unfold_locs here?
       Great question! Short answer: I can't design APIs.
       Long answer: in the simple checker it is much easier to treat
       dereferences in alias expressions as a read, which then gets
       flagged as an unfold (instead of a write, which is an fold). So we allow
       this strangeness until I inevitably mix this up *)
    let is_fold = IntSet.mem e_id ctxt.iso.unfold_locs in
    (* now make a fresh type for the location referred to by ap and rooted at v1 *)
    (* We generate the type for v1 within this map so as to use merge_types, which ensures our
       free variables are tighter.
       We return back:
       fresh context, old ap type (ownership met), fresh ap type (ownership met), substitution
       for variables in the types, fresh v1 types (ownership met), and a flag indicating
       we must force predicate generation
    *)
    let (ctxt',t2_sub,t2_sub',subst,t1',force_v1_cons),t2' = map_ap_with_bindings ap [] (fun (fv,subst) t ->
        let (c1,t') = merge_types ~loc ~path:ap ~bind_seed:(fv,subst) ~unfold_t2:is_fold ~t1:t1 ~t2:t ctxt in
        let const_subst = List.filter (fun (_,c) -> Paths.is_const_ap c) subst in
        let force_v1_cons = List.length const_subst <> List.length subst in
        let (c2,t1') = merge_types ~loc ~path:(`AVar v1) ~e1_expl:const_subst ~unfold_t1:is_fold ~t1:t ~t2:t1 c1 in
        let pre_t2_sub = meet_ownership e_id ap t ctxt in
        let post_t2_sub = meet_ownership next_id ap t' ctxt in
        let post_t1 = meet_ownership next_id (`AVar v1) t1' ctxt in
        (c2,pre_t2_sub,post_t2_sub,subst,post_t1,force_v1_cons),post_t2_sub
      ) lkp
    in
    (* now t1' and t2' refer to the same sets of free variables: any symbolic variables
       appearing in t1' and t2' are bound by tuple types
       
       Finally, we may have to unfold t2' to generate correct constraints
    *)
    let (t2_constr,t2_constr') = if is_fold then (unfold_once t2_sub,unfold_once t2_sub') else (t2_sub,t2_sub') in
    let app_matrix = apply_matrix ~t1 ~t2_bind:subst ~t2:t2_constr in
    let rec up_ap ap t2_base' ctxt = match ap with
      | `APre _ -> assert false
      | `AVar v -> update_type v t2_base' ctxt
      | `ADeref ap
      | `AProj (ap,_) -> up_ap ap t2_base' ctxt
    in
    do_with_context ctxt' @@
      let%bind psub2 = app_matrix ~force_cons:is_fold ~out_root:ap ~out_bind:subst ~out_type:t2_constr' in
      let%bind psub1 = app_matrix ~force_cons:force_v1_cons ~out_root:(`AVar v1) ~out_type:t1' in
      return_mut
      <|> shuffle_owners t1 t2_constr t1' t2_constr'
      <|> up_ap ap @@ sub_pdef psub2 t2'
      <|> update_type v1 @@ sub_pdef psub1 t1'
      <|> remove_sub psub1
      <|> remove_sub psub2
      <|> process_expr ?output_args ?output_type ~remove_scope cont

  | Cond(v,e1,e2) ->
    let add_pc_refinement cond ctxt =
      let curr_ref = lkp v in
      let branch_refinement = {
        rel_op1 = Nu;
        rel_cond = cond;
        rel_op2 = RConst 0
      } in
      ctxt |>
      update_type v @@ map_refinement (fun r -> And (r,Relation branch_refinement)) curr_ref
    in
    let fv_seed = if SS.mem v remove_scope then [] else [`AVar v] in
    process_conditional
      ~fv_seed
      ?output_args
      ?output_type ~remove_scope
      ~tr_path:(add_pc_refinement "=")
      ~fl_path:(add_pc_refinement "!=")
      e_id e1 e2 ctxt

  | NCond (v,e1,e2) ->
    process_conditional
      ?output_args
      ?output_type ~remove_scope
      ~tr_path:(fun ctxt ->
        let (ctxt',t) = make_fresh_type ~ground:true ~target_var:(`AVar v) ~loc:(LNull e_id) ~fv:[] (lkp v) ctxt in
        update_type v t ctxt'
      )
      ~fl_path:Fun.id e_id e1 e2 ctxt

  | EAnnot (ty_env,next) ->
    let env' =
      List.fold_left (fun acc (k,v) ->
        StringMap.add k v acc
      ) StringMap.empty ty_env in
    process_expr ?output_args ?output_type ~remove_scope next { ctxt with gamma = env' }

and process_conditional ?output_args ?output_type ?(fv_seed=[]) ~remove_scope ~tr_path ~fl_path e_id e1 e2 ctxt =
  let ctxt1 = process_expr ?output_args ?output_type ~remove_scope e1 @@ tr_path ctxt in
  let ctxt2 = process_expr ?output_args ?output_type ~remove_scope e2 @@ fl_path {
        ctxt with
        refinements = ctxt1.refinements;
        v_counter = ctxt1.v_counter;
        ownership = ctxt1.ownership;
        pred_arity = ctxt1.pred_arity;
        ovars = ctxt1.ovars
      } in
  let loc = LCond e_id in
  let u_ctxt = { ctxt2 with gamma = SM.empty } in
  let b1 = SM.bindings ctxt1.gamma in
  let b2 = SM.bindings ctxt2.gamma in
  let dg1 = denote_gamma ctxt1.gamma in
  let dg2 = denote_gamma ctxt2.gamma in
  let subsume_types ctxt ~target_var t1 t2 =
    let ctxt',t'fresh = merge_types ~bind_seed:(fv_seed,[]) ~loc ~path:(`AVar target_var) ~t1 ~t2 ctxt in
    let t' = t'fresh in
    let c_up =
      add_var_type_implication dg1 target_var t1 t' ctxt'
      |> add_var_type_implication dg2 target_var t2 t'
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
    
and process_call ~e_id ~cont_id ctxt c =
  let arg_bindings = List.mapi (fun i k ->
      (i,k,SM.find k ctxt.gamma)) c.arg_names
  in
  let pre_map s = "reif!" ^ s in
  let inst_fn_type = instantiate_fn_type ~lbl:c.label ~pre_map c.arg_names in
  let input_env = ctxt.gamma |> denote_gamma in
  let callee_type = SM.find c.callee ctxt.theta in
  let concr_in_t =
    List.map inst_fn_type callee_type.arg_types
    |> List.map2 (Fun.flip compile_type) c.arg_names
    |> List.mapi (fun i t ->
        meet_arg i c.callee ctxt t
      )
  in
  let symb_out_t : typ list = List.map inst_fn_type callee_type.output_types in
  let in_out_types = List.combine concr_in_t symb_out_t in
  let rec is_reified = function
    | `APre s -> StringExt.starts_with s "reif!"
    | `AVar _ -> false
    | `AElem ap
    | `AInd ap
    | `ALen ap
    | `ADeref ap
    | `AProj (ap,_) -> is_reified ap
    | `AFree _ -> assert false
  in
  let updated_ctxt = List.fold_left2 (fun acc (i,k,arg_t) (in_t,out_t) ->
      do_with_context acc @@
        let loc = LCall (c.label,k) in
        let concretize_arg_t t = compile_type t k |> with_refl (`AVar k) in
        let constrain_in t ctxt =
          let concr_arg_type = concretize_arg_t t in
          add_type_implication input_env concr_arg_type in_t ctxt
          |> constrain_owner concr_arg_type in_t
        in
        let ap = `AVar k in
        let%swith arg_t_o = meet_ownership e_id ap arg_t in
        let%bind (resid,formal) = split_arg arg_t_o in_t in
        let%swith out_owner = meet_out i c.callee out_t in
        (* the (to be) summed type, shape equiv to resid_eq and out_t_eq *)
        let%bind fresh_type_ = merge_types ~fv_filter:(fun p ->
            not (is_reified p)
          ) ~loc ~path:ap ~t1:out_owner ~t2:resid in
        let%swith fresh_type_own = meet_ownership cont_id ap fresh_type_ in
        let concr_arg_type = concretize_arg_t arg_t in
        let pre_types = fold_with_bindings (fun ~pos p _ r a ->
            if add_post_type_p pos p then
              (Paths.pre (Paths.map_root pre_map p),with_pred_refl p r,`NUnk)::a
            else
              a
          ) (`AVar k) ([],[]) concr_arg_type [] in

        let force_cons = post_update_type arg_t in

        let close_pre_env ({ante; conseq; env;_ } as constr) =
          let collect_pre_refs r a =
            fold_refinement_args ~rel_arg:(fun a p ->
              if Paths.is_pre p then
                Paths.PathSet.add p a
              else
                a
            ) ~pred_arg:(fun a (pl,_) ->
              List.fold_left (fun acc p ->
                if Paths.is_pre p then
                  Paths.PathSet.add p acc
                else
                  acc
              ) a pl
            ) a r
          in
          let seed =
            Paths.PathSet.empty
            |> collect_pre_refs ante
            |> collect_pre_refs conseq
          in
          let ref_pre =  List.fold_left (fun acc (_,p,_) -> collect_pre_refs p acc) seed env in
          let env' = List.fold_left (fun e ((p,_,_) as bind) ->
              if Paths.PathSet.mem p ref_pre then
                bind::e
              else
                e
            ) env pre_types
          in
          { constr with env = env' }
        in
        let%bind psub = apply_matrix
            ~pp_constr:(fun ~summary:_ _ constr  ->
              close_pre_env constr
            )
            ~t1:resid
            ~t2:out_owner
            ~force_cons
            ~out_root:ap
            ~out_type:fresh_type_own
        in
        (* now the magic *)
        return_mut
        (* constrain the formal half of the arg type *)
        <|> constrain_in formal
        <|> sum_ownership resid out_owner fresh_type_own
        <|> update_type k @@ sub_pdef psub fresh_type_own
        <|> remove_sub psub

    ) ctxt arg_bindings in_out_types
  in
  let result = inst_fn_type callee_type.result_type in
  (updated_ctxt, result)
and instantiate_fn_type ?lbl ?pre_map arg_names =
  let sub_map = List.mapi (fun i k ->
      (Printf.sprintf "$%d" i, k)
    ) arg_names
  in
  let map_predicate_arg = function
    | `Sym r -> `Sym r
    | (#Paths.concr_ap as ap) -> 
      let ap' = Paths.map_root (fun i -> List.assoc i sub_map) ap in
      Option.fold ~none:(ap' :> refine_ap) ~some:(fun pre_mapper ->
        if Paths.is_pre ap' then
          (Paths.map_root pre_mapper ap' :> refine_ap)
        else
          (ap' :> refine_ap)
      ) pre_map
  in
  let map_pred_args = List.map map_predicate_arg in
  let inst_symb = map_refinement_preds
      ~named:(fun nm args -> NamedPred (nm,map_pred_args args))
      ~ctxt:(fun _ _ _ -> assert false)
      ~pred:(fun nm args ->
        match lbl with
        | Some l -> CtxtPred (l,nm,map_pred_args args)
        | None -> Pred (nm, map_pred_args args))
      ~rel_arg:map_predicate_arg
  in
  fun t ->
    map_refinement inst_symb t

let process_function_bind ctxt fdef =
  let arg_names = fdef.args in
  let inst_fn_type = instantiate_fn_type arg_names in
  let f_typ = SM.find fdef.name ctxt.theta in
  let typ_template = List.combine arg_names f_typ.arg_types in
  let init_env = List.fold_left (fun g (n,t) ->
      let inst = inst_fn_type t in
      let (g',inst') =
        walk_with_path (fun ~pos path p g ->
          if not (add_post_type_p pos path) then
            (g,p)
          else
            let pre_path = P.pre path in
            let pre_var = P.to_z3_ident pre_path in
            (SM.add pre_var (Int Top) g, And (p, Relation { rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (pre_path :> refine_ap) }))
            
        ) (`AVar n) inst g
      in
      SM.add n inst' g'
    ) SM.empty typ_template
  in
  let result_type = inst_fn_type f_typ.result_type in
  let out_typ_template = List.combine arg_names f_typ.output_types in
  let output_args = List.map (fun (v,out_ty_tmpl) ->
      let out_refine_type = inst_fn_type out_ty_tmpl in
      (v,out_refine_type)
    ) out_typ_template in
  let ctxt' = process_expr ~output_args ~output_type:result_type ~remove_scope:SS.empty fdef.body { ctxt with gamma = init_env } in
  ctxt'

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

let propagate_grounding refine pred =
  let seed = StringMap.bindings pred |> List.filter (fun (_,(b,_)) -> b) |> List.map fst |> StringSet.of_list in
  let rec get_pred_name = function
    | Pred (nm,_)
    | CtxtPred (_,nm,_) -> StringSet.singleton nm
    | And (r1,r2) -> StringSet.union (get_pred_name r1) (get_pred_name r2)
    | _ -> StringSet.empty
  in
  let rec propagate_loop s =
    let c = StringSet.cardinal s in
    let s' = List.fold_left (fun acc {ante; conseq; nullity; _ } ->
        if nullity = `NLive then
          acc
        else
          let ante_nm = get_pred_name ante in
          if StringSet.is_empty @@ StringSet.inter acc ante_nm then
            acc
          else
            StringSet.union acc @@ get_pred_name conseq
      ) s refine
    in
    if c = (StringSet.cardinal s') then
      s'
    else
      propagate_loop s'
  in
  let to_ground = propagate_loop seed in
  StringMap.mapi (fun k (_,n) ->
    (StringSet.mem k to_ground,n)
  ) pred

let infer ~print_pred ~save_types ?o_solve ~intrinsics (st,type_hints,iso) (fns,main) =
  let init_fun_type f_def =
    let lift_simple_type ~post ~loc =
      lift_to_refinement ~pred:(fun ~mu ~pos fv path ->
        let fv' =
          if post && (add_post_type_p pos path) then
            ((Paths.pre path) :> refine_ap)::fv
          else
            fv
        in
        make_fresh_pred ~mu ~ground:pos.under_mu ~pred_vars:(fv',path) ~loc
      )
    in
    let gen_arg_preds ~post ~loc fv arg_templ = mmap (fun (k,t) ->
        let fv' = List.filter (function
          | `AVar v when v = k -> false
          | _ -> true) fv in
        let%bind t' = lift_simple_type ~post ~loc:(loc k) (`AVar k) fv' t in
        return @@ t'
      ) arg_templ
    in
    let simple_ftype = SM.find f_def.name st in
    let symbolic_args = List.mapi (fun i _ -> Printf.sprintf "$%d" i) f_def.args in
    let arg_templ = List.combine symbolic_args simple_ftype.SimpleTypes.arg_types in
    let free_vars = List.filter (fun (_,t) -> t = `Int) arg_templ |> List.map (fun (n,_) -> (`AVar n)) in
    let%bind arg_types = gen_arg_preds ~post:false ~loc:(fun k -> LArg (f_def.name,k)) free_vars arg_templ in
    let%bind output_types = gen_arg_preds ~post:true ~loc:(fun k -> LOutput (f_def.name,k)) free_vars arg_templ in
    let%bind result_type =
      lift_simple_type ~post:false (`AVar "RET") ~loc:(LReturn f_def.name) free_vars simple_ftype.SimpleTypes.ret_type
    in
    map_state (fun ctxt -> 
      { ctxt with
        theta = SM.add f_def.name {
            arg_types; output_types; result_type
          } ctxt.theta
      })
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
    pred_arity = StringMap.empty;
    v_counter = 0;
    pred_detail = Hashtbl.create 10;
    store_env;
    o_info = (match o_solve with
    | Some e -> e
    | None -> (Hashtbl.create 10,SM.empty));
    type_hints;
    iso
  } in
  let ctxt = List.fold_left (Fun.flip init_fun_type) initial_ctxt fns in
  let { pred_detail; refinements; ownership; ovars; pred_arity; theta; _ } =
    List.fold_left process_function ctxt fns
    |> process_expr main
  in
  let pred_arity = propagate_grounding refinements pred_arity in
  if print_pred then print_pred_details pred_detail;
  Result.{
    ownership;
    ovars;
    refinements;
    theta;
    arity = pred_arity;
    ty_envs 
  }

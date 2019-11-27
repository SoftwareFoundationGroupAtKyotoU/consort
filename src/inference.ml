open Ast
open RefinementTypes
open Sexplib.Std
open Std
open Std.StateMonad
open SimpleChecker.SideAnalysis
    
module SM = StringMap
module SS = StringSet
module P = Paths

module OI = OwnershipInference

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
  | LFold of int [@@deriving sexp]

type funenv = funtype SM.t
type tenv = typ SM.t

let sexp_of_tenv = SM.sexp_of_t ~v:sexp_of_typ

let string_of_concr_refinement =
  PrettyPrint.pp_gen_rev (pp_ref (fun (k,_) ->
      pp_alist (k :> refine_ap list)
    ))[@@ocaml.warning "-32"]

type tcon = {
  env: (Paths.concr_ap * concr_refinement * (concr_nullity list)) list;
  ante: concr_refinement;
  conseq: concr_refinement;
  nullity: concr_nullity list;
  target: Paths.concr_ap option
}[@@deriving sexp]

exception Incompleteness of string

type context = {
  theta: funenv;
  gamma: tenv;
  refinements: tcon list;
  pred_arity: (bool * int) StringMap.t;
  v_counter: int;
  store_env: int -> tenv -> unit;
  iso: SimpleChecker.SideAnalysis.results;
  o_hints: float OI.ownership_ops;
}

type ('i,'o) osrc =
  | Prev : (bool,bool) osrc
  | Ownership : OI.magic_loc -> ('a,bool) osrc

module Result = struct
  type t = {
    theta: funenv;
    refinements: tcon list;
    arity: (bool * int) StringMap.t;
    ty_envs: (int,tenv) Hashtbl.t
  }
end

let mk_counter () =
  let counter = ref 0 in
  fun () ->
    let nxt = !counter in
    incr counter;
    nxt

let fresh_tvar  = mk_counter ()

let type_mismatch t1 t2 =
  let tag1 = Obj.repr t1 |> Obj.tag in
  let tag2 = Obj.repr t2 |> Obj.tag in
  (assert (tag1 <> tag2); failwith "Mismatched types")

let unsupported s = raise @@ Incompleteness s

let do_with f l = ignore (f l); l

let ignore_iref = (fun r _ -> r),(fun _ r -> r)

let update_map v t m =
  SM.remove v m
  |> SM.add v t

let update_type v t ctxt =
  { ctxt with gamma = update_map v t ctxt.gamma }

let%lm mupdate_type v t ctxt = update_type v t ctxt

let add_type v t ctxt =
  let te =
    SM.add v t ctxt.gamma
  in
  { ctxt with gamma = te }

let update_array_bind arr_bind root b =
  (bind_of_arr arr_bind root) @ b

let update_tuple_bind t_bind root b1 =
  (compile_bindings t_bind root) @ b1

let update_array_env ~nullity env path bind len_r =
  let len_ap = (P.len path) in
  let len_comp = compile_refinement len_ap bind len_r in
  let ind_ap = (P.ind path) in
  [
    (len_ap,len_comp,nullity);
    (ind_ap, NamedPred ("valid-ind", ([ len_ap ],ind_ap)), nullity)
  ] @ env

let update_tuple_env ~nullity env root bind b tl =
  List.fold_left (fun acc (_,p) ->
    match p with
    | SVar _ -> acc
    | SProj i ->
      let cap = P.t_ind root i in
      let t_ref = match List.nth tl i with
        | Int r -> r
        | _ -> assert false
      in
      (cap,compile_refinement cap bind t_ref,nullity)::acc
  ) env b

(* this denotes CONSTANT PATHS ONLY *)
let rec denote_type path (bind: (int * Paths.concr_ap) list) acc t =
  match t with
  | Array (b,len_r,_,et) ->
    let arr_b = update_array_bind b path bind in
    let acc' = update_array_env ~nullity:[] acc path bind len_r in
    denote_type (P.elem path) arr_b acc' et
  | Ref (_,_,_) -> acc
  | Int r ->
    let comp_r = compile_refinement path bind r in
    (path,comp_r,[])::acc
  | Tuple (b,t) ->
    let (bind' : (int * Paths.concr_ap) list) = update_tuple_bind b path bind in
    fold_lefti (fun i acc te -> 
      denote_type (P.t_ind path i) bind' acc te
    ) acc t
  | TVar _ -> acc
  | Mu (_,_,_,_) -> acc

let denote_gamma gamma =
  SM.fold (fun v t acc ->
    denote_type (P.var v) [] acc t
  ) gamma []

let denote_gamma_m ctxt = (ctxt,denote_gamma ctxt.gamma)

let%lq gen_own loc p ctxt =
  let f = OI.GenMap.find (loc,p) ctxt.o_hints.OI.gen in
  f > 0.0

let%lq split_own loc p ctxt =
  let (f1,f2) = OI.SplitMap.find (loc,p) ctxt.o_hints.OI.splits in
  (f1 > 0.0, f2 > 0.0)


let mtmap p f l = mmapi (fun i e ->
    f (P.t_ind p i) e
  ) l

let rec to_top_type = function
  | TVar id -> TVar id
  | Int _ -> Int Top
  | Ref (t,_,_) ->
    Ref (to_top_type t,false,NUnk)
  | Tuple (b,tl) ->
    Tuple (b,List.map to_top_type tl)
  | Array (a,_,_,t) ->
    Array (a,Top,false,to_top_type t)
  | Mu (s,{fv_map; pred_symbols},id,t) ->
    Mu (s,{fv_map; pred_symbols = List.map (fun (ma,_) ->
               (ma, Top)
             ) pred_symbols},id,to_top_type t)

let rec split_by_own loc p o1 o2 t =
  if o1 && o2 then
    split_type loc p t
  else if o1 then
    return (t,to_top_type t)
  else if o2 then
    return (to_top_type t,t)
  else
    return (to_top_type t,to_top_type t)
and split_type loc p t =
  match t with
  | Int _ -> return (t,t)
  | Ref (t,_,n) ->
    let%bind (o1,o2) = split_own loc p in
    let%bind (t1,t2) = split_by_own loc (P.deref p) o1 o2 t in
    return ((Ref (t1,o1,n), Ref (t2,o2,n)))
  | Array (b,len_r,_,et) ->
    let%bind (o1,o2) = split_own loc p in
    let%bind (et1,et2) = split_by_own loc (P.elem p) o1 o2 et in
    return  (Array (b,len_r,o1,et1), Array (b,len_r,o2,et2))
  | Tuple (b,tl) ->
    let%bind split_tl = mtmap p (split_type loc) tl in
    let (tl1,tl2) = List.split split_tl in
    return (Tuple (b,tl1),Tuple (b,tl2))
  | TVar id -> return (TVar id,TVar id)
  | Mu (a,n,i,t) ->
    let%bind (t1,t2) = split_type loc p t in
    return (Mu (a,n,i,t1), Mu (a,n,i,t2))

let add_constraint gamma ?ante_ext path ante conseq nullity ctxt =
  { ctxt with
    refinements = {
      env = gamma;
      ante = Option.fold ~some:(fun r -> And (r,ante)) ~none:ante ante_ext;
      conseq;
      nullity;
      target = Some path
    }::ctxt.refinements
  }

let%lm add_type_implication ?(path_filter=(fun _ -> true)) ?(init_bind=[]) ?ante_ext gamma root t1_ t2_ ctxt_ =
  let add_constraint_local gamma path c1 c2 nullity ctxt =
    if path_filter path then
      add_constraint ?ante_ext gamma path c1 c2 nullity ctxt
    else
      ctxt
  in
  let fresh_nvar = mk_counter () in
  let rec impl_loop ~nullity gamma_curr path b1 b2 t1 t2 ctxt =
    match t1,t2 with
    | Int r1, Int r2 ->
      let c1 = compile_refinement path b1 r1 in
      let c2 = compile_refinement path b2 r2 in
      add_constraint_local gamma_curr path c1 c2 nullity ctxt
        
    | Array (ab1,len_r1,_,et1), Array (ab2,len_r2,_,et2) ->
      let clen1 = compile_refinement (P.len path) b1 len_r1 in
      let clen2 = compile_refinement (P.len path) b2 len_r2 in
      let b1' = update_array_bind ab1 path b1 in
      let b2' = update_array_bind ab2 path b2 in
      let gamma' = update_array_env ~nullity gamma_curr path b1 len_r1 in
      let ctxt' = add_constraint_local gamma_curr (P.len path) clen1 clen2 nullity ctxt in
      impl_loop ~nullity gamma' (P.elem path) b1' b2' et1 et2 ctxt'

    | Ref (t1',_,n), Ref (t2',_,_) ->
      let n' =
        match n with
        | NLive -> `NLive
        | NNull -> `NNull
        | NUnk -> `NVar (fresh_nvar ())
      in
      impl_loop ~nullity:(n'::nullity) gamma_curr (P.deref path) b1 b2  t1' t2' ctxt

    | Tuple (bt1,tl1), Tuple (bt2,tl2) ->
      let b1' = update_tuple_bind bt1 path b1 in
      let b2' = update_tuple_bind bt2 path b2 in
      let env' = update_tuple_env ~nullity gamma_curr path b1' bt1 tl1 in
      fold_left2i (fun i acc te1 te2 ->
        impl_loop ~nullity env' (P.t_ind path i) b1' b2' te1 te2 acc
      ) ctxt tl1 tl2
        
    | TVar _,TVar _ -> ctxt
      
    | Mu (_,_,_,t1'), Mu (_,_,_,t2') ->
      impl_loop ~nullity gamma_curr path b1 b2 t1' t2' ctxt
    | t1,t2 -> type_mismatch t1 t2
  in
  impl_loop ~nullity:[] gamma root init_bind init_bind t1_ t2_ ctxt_

let add_var_type_implication dg var t1 t2 ctxt =
  add_type_implication dg (P.var var) t1 t2 ctxt

let add_var_implication dg gamma var t ctxt =
  add_var_type_implication dg var (SM.find var gamma) t ctxt
  
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
  | MProj (m_ap,i) -> P.t_ind (root_mu_path path m_ap) i
  | MDeref m_ap -> P.deref @@ root_mu_path path m_ap
  | MElem m_ap -> P.elem @@ root_mu_path path m_ap
  | MLen m_ap -> P.len @@ root_mu_path path m_ap

let mu_bind_update_cb =
  let apply_bind_set path {fv_map; pred_symbols}  (ctxt,(bind_set,_)) =
    let ps' = List.map (fun (m_ap,r) ->
        let c_ap = root_mu_path path m_ap in
        let new_r = Paths.PathMap.find_opt c_ap bind_set in
        match new_r with
        | Some r' -> (m_ap,r')
        | None -> (m_ap, r)
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

let plift (f: ('a,'b,'c) Let_syntax.context_monad)  ((ctxt,(ps,fv)) : ('b * ('d * 'e))) : ('c * ('d * 'e)) * 'a =
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
      return_with_path (Paths.PathMap.add path ind_pred path_set,fv_manager) (And (ind_pred,local_pred))

let is_max_ref pos = (List.nth_opt pos.olist 0) = Some false

let generate_type (type a) ~ground ~os:(os: (a,bool) osrc) ~target ~loc ~fv_seed ?(bind=[]) ~fv_gen t context =
  let o_map : a -> Paths.concr_ap -> (bool,'c,'c) Let_syntax.context_monad = match os with
    | Prev -> (fun o _ -> return o)
    | Ownership loc -> (fun _ p ->
        plift @@ gen_own loc p
      )
  in
  let ((ctxt,_),t') =
    walk_with_bindings_own ~o_map:o_map ~mu_map:mu_bind_update_cb 
      (fun ~pos root (fv,bind) r ->
        let is_top = is_max_ref pos in
        if is_top then
          return Top
        else
          let fv_add = fv_gen root fv r in
          generate_refinement ~loc ~ground ~pos (fv_add,bind) root
      ) target (fv_seed,bind) t (context,initial_walk_state)
  in
  (ctxt,t')

let make_fresh_type (type a) ~os:(os: (a,bool) osrc) ?(ground=false) ~target_var ~loc ~fv ?(bind=[]) =  
  generate_type ~os ~ground ~target:target_var ~loc ~fv_seed:fv ~bind ~fv_gen:(fun _ fv _ ->
    fv
  )

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
      | Int _ -> (`Concr (P.var k))::acc
      | Array _ -> (`Concr (P.len (P.var k)))::acc
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

let rec make_null = function
  | Ref (t,o,_) ->
    Ref (make_null t,o,NNull)
  | Tuple (b,tl) ->
    Tuple (b,List.map make_null tl)
  | Int r -> Int r
  | TVar id -> TVar id
  | Mu (a,b,c,t) -> Mu (a,b,c,make_null t)
  | Array (a,lr,o,t) ->
    Array (a,lr,o,make_null t)

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
let lift_to_refinement loc ~nullity ~pred initial_path fv t =
  let rec lift_to_skeleton t =
    match t with
    | `Int -> Int ()
    | `Ref t' -> Ref (lift_to_skeleton t', (), nullity)
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
  let rec push_subst mu_type (abs_path,mu_path) in_scope (t: (unit, unit, unit,nullity) RefinementTypes._typ) =
    match t with
    | TVar id ->
      let%bind () = mutate (fun st -> ([],st,[])) in
      let%bind unfolded = do_subst in_scope mu_type in
      let%bind (sub_map,st',scope_map) = get_state in
      let%bind () = put_state st' in
      return @@ Mu (sub_map,scope_map,id,unfolded)
    | Mu (_,_,_,_) -> raise @@ Incompleteness "NESTED! TYPES!"
    | Ref (t,(),n) ->
      let%bind t' = push_subst mu_type (P.deref abs_path, MDeref mu_path) in_scope t in
      return @@ Ref (t',(),n)
    | Int () ->
      let%bind () = put_app (abs_path,mu_path) in
      return @@ Int ()
    | Array (b,(),(),t) ->
      let%bind () = put_app (P.len abs_path,MLen mu_path) in
      let%bind t' = push_subst mu_type (P.elem abs_path, MElem mu_path) (in_scope @ [b.ind;b.len]) t in
      return @@ Array (b,(),(),t')
    | Tuple (b,tl) ->
      let in_scope' = in_scope @ (List.map fst b) in
      let%bind tl' = mmapi (fun i t_e ->
          push_subst mu_type (P.t_ind abs_path i, MProj (mu_path,i)) in_scope' t_e
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
      let%bind t' = unfold_once (P.elem path) t in
      return @@ Array (a,b,c,t')
    | Tuple (b,tl) ->
      let%bind tl' = mmapi (fun i te ->
          unfold_once (P.t_ind path i) te
        ) tl
      in
      return @@ Tuple (b,tl')
    | Ref (t,(),n) ->
      let%bind t' = unfold_once (P.deref path) t in
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
        (mu_ap,Paths.PathMap.find (root_mu_path path mu_ap) bound_map)
      ) fv_list
    in
    let%bind () = put_state (ctxt,None,None) in
    return @@ { pred_symbols; fv_map = fv_list }
  in
  
  let mu_map = pre_mu,post_mu in

  let maybe_add pos path r (ctxt,fv_map,bound_map) =
    if pos.under_mu then
      (ctxt,fv_map,Option.map (P.PathMap.add path r) bound_map),r
    else
      (ctxt,fv_map,bound_map),r
  in

  let%bind t_inst = walk_with_bindings_own ~o_map:(fun () path (ctxt,f,p) ->
      let (ctxt',o) = gen_own loc path ctxt in
      (ctxt',f,p),o
    ) ~mu_map (fun ~pos root (fv_loc,_) () ->
      if (List.nth_opt pos.olist 0) = Some false then
        maybe_add pos root Top
      else if pos.under_mu then
        let%bind (ctxt,fv_map,bound_map) = get_state in
        let (ol,il) = Paths.PathMap.find root @@ Option.get fv_map in
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
    walk_with_bindings_own ~o_map:(fun c _ -> return c)
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
  let%bind () = put_state ctxt' in
  return applied

let lift_src_ap = function
  | AVar v -> P.var v
  | ADeref v -> P.deref (P.var v)
  | AProj (v,i) -> P.t_ind (P.var v) i
  | APtrProj (v,i) -> P.t_ind (P.deref (P.var v)) i


let get_ref_aps_gen proj =
  fold_refinement_args
    ~rel_arg:(fun l ap -> ap::l)
    ~pred_arg:(fun l ap -> proj ap @ l) []
   
let get_ref_aps = get_ref_aps_gen fst

(* t2 is the type to be copied w.r.t mu, tuple binding, etc. *)
let merge_types ~gloc ~loc ~path ?(fv_filter=(fun _ -> true)) ?(e1_expl=[]) ?(bind_seed=([],[])) ?(unfold_t1=false) ?(unfold_t2=false) ~t1 ~t2 ctxt =
  let filter_expl em = List.filter_map (function
    | `Sym i -> if List.mem_assoc i em then
        Some (List.assoc i em)
      else None
    | `Concr c -> Some c)
  in
  let counter = mk_counter () in
  
  let gen_ref expl r =
    let fv_set = get_ref_aps_gen Fun.id r |> filter_expl expl |> List.filter fv_filter |> Paths.PathSet.of_list in
    let id = counter () in
    (id,fv_set)
  in
  let nullity_counter = mk_counter () in
  let rec to_type_template expl = function
    | Int r ->
      Int (gen_ref expl r)
    | Ref (r,_,n) ->
      Ref (to_type_template expl r, nullity_counter (), n)
    | Mu (a,{pred_symbols;fv_map},i,t) ->
      Mu (a,{
            pred_symbols = List.map (fun (a,_) -> (a,Top)) pred_symbols; fv_map
          },i,to_type_template expl t)
    | TVar id -> TVar id
    | Tuple (b,tl) ->
      let expl' = List.fold_left (fun acc (i,p) ->
          match p with
          | SProj _ -> acc
          | SVar v -> (i,P.var v)::acc
        ) expl b in
      Tuple (b,List.map (to_type_template expl') tl)
    | Array (b,l,_,t) ->
      (* we don't use the id below, it's just for the types to work out *)
      Array (b,gen_ref expl l,nullity_counter (),to_type_template expl t)
      
  in
  let t1_fv_templ = to_type_template e1_expl t1 in
  let t2_fv_templ = to_type_template [] t2 in
  (* IT'S AN N2 MINE *)
  let merge_nullity id n1 n2 nmap =
    IntMap.update id (fun bind ->
      let join_n = join_nullity n1 n2 in
      Some (Option.fold ~none:join_n ~some:(join_nullity join_n) bind)
    ) nmap
  in
  let merge_fvs (_,r1) (id,r2) map =
    IntMap.update id (fun bind ->
      Option.value ~default:(Paths.PathSet.empty) bind
      |> Paths.PathSet.union @@ Paths.PathSet.union r1 r2
      |> Option.some) map
  in
  let rec merge_loop t1_templ t2_templ ((fv_map,n_map) as map) =
    match t1_templ, t2_templ with
    | Int r1,Int r2 -> (merge_fvs r1 r2 fv_map,n_map)
    | Mu (_,_,_,t1), Mu (_,_,_,t2) ->
      merge_loop t1 t2 map
    | Ref (t1,_,n1), Ref (t2,id,n2) -> merge_loop t1 t2 (fv_map, merge_nullity id n1 n2 n_map)
    | Array (_,l1,_,t1), Array (_,l2,_,t2) ->
      merge_loop t1 t2 (merge_fvs l1 l2 fv_map,n_map)
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 (fun acc t1 t2 ->
          merge_loop t1 t2 acc
        ) map tl1 tl2
    | TVar _,TVar _ -> map
    | _,_ -> type_mismatch t1_templ t2_templ
  in
  let maybe_unfold f t =
    if f then
      unfold_once_gen (unfold_gen ~gen:fresh_tvar ~iref:ignore_iref ~rmap:(fun _ r -> r)) t
    else
      t
  in
  let (merge_map,n_map) =
    merge_loop
      (maybe_unfold unfold_t1 t1_fv_templ)
      (maybe_unfold unfold_t2 t2_fv_templ)
      (IntMap.empty,IntMap.empty)
  in
  let rec apply_nullity t =
    match t with
    | TVar id -> TVar id
    | Int r -> Int r
    | Array (a,lr,_,t) ->
      Array (a,lr,(),apply_nullity t)
    | Ref (t,id,_) ->
      Ref (apply_nullity t,(),IntMap.find id n_map)
    | Mu (ar,fv,i,t) ->
      Mu (ar,fv,i,apply_nullity t)
    | Tuple (b,tl) ->
      Tuple (b,List.map apply_nullity tl)
  in
  let t2_templ_appn = apply_nullity t2_fv_templ in
  let (fv_seed,bind) = bind_seed in
  generate_type ~os:(Ownership gloc) ~ground:false ~target:path ~loc ~fv_seed ~bind ~fv_gen:(fun _ sym_fv (id,_) ->
    (List.map (fun l -> `Concr l) @@ Paths.PathSet.elements @@ IntMap.find id merge_map) @ sym_fv
  ) t2_templ_appn ctxt

let inject_mu (get,put) (f1,f2) =
  let inj1 =
    (fun r ar fv ctxt ->
      let (c1,rem) = get ctxt in
      let (c1',ret) = f1 r ar fv c1 in
      let c_ret = put c1' rem in
      (c_ret,ret)
    )
  in
  let inj2 =
    (fun p fv ctxt ->
      let (c1,rem) = get ctxt in
      let (c1',ret) = f2 p fv c1 in
      let c_ret = put c1' rem in
      (c_ret,ret)
    )
  in
  (inj1,inj2)

let remove_var_from_pred ~loc ~mk_fv ~oracle ~pos path (sym_vars,sym_val) r =
  let curr_comp = compile_refinement path sym_val r in
  if oracle curr_comp path then begin
    assert ((List.nth_opt pos.olist 0) <> Some false);
    let fv : refine_ap list = (mk_fv path curr_comp sym_vars sym_val) in
    (* extract out the update set *)
    let%bind (update_set : Paths.PathSet.t) = (fun (c1,c2) -> (c1,c2)) in
    let%bind new_pred = generate_refinement ~ground:false ~loc ~pos (fv,sym_val) path in
    let update_set' = Paths.PathSet.add path update_set in
    let%bind () = mutate (fun c -> (c,update_set')) in
    return new_pred
  end else
    return r

let remove_var_from_type ~loc ~oracle ~mk_fv root_var t context =
  let staged = remove_var_from_pred  ~mk_fv ~loc ~oracle in
  let type_gen_state = ((context,initial_walk_state),Paths.PathSet.empty) in
  let getput = (Fun.id,fun i j -> (i,j)) in
  let ((ctxt',_),impl_paths),t' = walk_with_bindings_own ~mu_map:(inject_mu getput mu_bind_update_cb) ~o_map:(fun c _ -> return c) staged root_var ([],[]) t type_gen_state in
  (ctxt',impl_paths),t'

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
                      (string_of_refinement r)
                else ()
              )
          |> do_with @@ List.iter @@ StrUF.register eq_ref
          |> do_with @@ Std.fold_left_fst (fun a ->
                do_with @@ StrUF.union eq_ref a)
          |> List.fold_left (Fun.flip Paths.PathSet.add) a
        ) (P.var var) ([],[]) (SM.find var ctxt.gamma) Paths.PathSet.empty
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
      |> List.filter outer_var_p |> List.map (fun l -> `Concr l)
    in
    concr_args @ sym_vars_filtered
  in
  let remove_fn = remove_var_from_type ~loc ~oracle:removal_oracle in
  
  let updated =
    SM.fold (fun v_name t c ->
      if SS.mem v_name to_remove then
        c
      else
        let ((c',impl_paths),t') = remove_fn ~mk_fv:(free_var_manager v_name) (P.var v_name) t c in
        let t_purge = purge_tuple_fv to_remove t' in
        let c'',() = add_type_implication ~path_filter:(fun p ->
            Paths.PathSet.mem p impl_paths
          ) curr_te (P.var v_name) t t_purge c' in
        { c'' with gamma = SM.add v_name t_purge c''.gamma }
    ) ctxt.gamma { ctxt with gamma = SM.empty }
  in
  updated

let lift_imm_op_to_rel = function
  | IVar v -> RAp ((P.var v) :> concr_ap)
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
          rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr target)
        })
    in
    Int r'
  | Array (b,l,o,t) ->
    let l' = And (l, Relation {
           rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr (P.len target))
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
  binding: (int * concr_ap) list;
  env: (Paths.concr_ap * concr_refinement * (concr_nullity list)) list;
  path: concr_ap;
  nullity_stack : concr_nullity list;
  sym_bindings: (int * refine_ap) list;
}

let step_tup wc ?b_out:out_o b tl =
  let binding = update_tuple_bind b wc.path wc.binding in
  let sym_bindings = Option.map (fun l ->
      List.map (function
      | (tv,SProj i) ->
        let out_tvar = List.find (function
          | (_,SProj i') -> i = i'
          | _ -> false
          ) l |> fst
        in
        tv,`Sym out_tvar
      | tv,SVar v -> (tv,`Concr (P.var v))
      ) b
    ) out_o
    |> Option.fold ~none:wc.sym_bindings ~some:(fun l -> l @ wc.sym_bindings)
  in
  let env = update_tuple_env ~nullity:wc.nullity_stack wc.env wc.path binding b tl in
  fun i t ->
    ({ wc with
       path = P.t_ind wc.path i;
       binding;
       env;
       sym_bindings
     },t)
    
let step_ref nxt wc t n =
  let concr_n =
    match n with
    | NLive -> `NLive
    | NNull -> `NNull
    | NUnk -> `NVar (nxt ())
  in
  ({
    wc with
    path = P.deref wc.path;
    nullity_stack = concr_n::wc.nullity_stack
  },t)

let ctxt_compile_ref wc =
  compile_refinement wc.path wc.binding

let unsafe_extract_pred = function
  | Pred (i,(fv,_)) -> (i,fv)
  | _ -> failwith "You broke an invariant somewhere I guess :("

let unsafe_split_ref = function
  | Ref (r,o,n) -> r,o,n
  | _ -> failwith "You were supposed to give me a ref :("
let step_array wc b len_ref t =
  { wc with
    path = P.elem wc.path;
    binding = update_array_bind b wc.path wc.binding;
    env = update_array_env ~nullity:wc.nullity_stack wc.env wc.path wc.binding len_ref
  },t

(* apply_matrix walks t1, t2 and out_type in parallel. At each leaf
   node, it generates a constrain on out_type's refinements based
   on the ownerships along the paths from the roots of t1 and t2 to the leaf.
*)
let apply_matrix ?(env_seed=[]) ?pp_constr ~t1 ?(t2_bind=[]) ~t2 ?(force_cons=true) ~out_root ?(out_bind=[]) ~out_type ctxt =
  let (g_0,filtered_scope) = denote_gamma ctxt.gamma
    |> List.partition (fun (p,_,_) ->
        not (Paths.has_prefix ~prefix:out_root p)
      )
  in
  let g = g_0 @ env_seed in
  let const_filtered = List.filter (fun (p,_,_) -> Paths.is_const_ap p) filtered_scope in
  let pp = match pp_constr with
    | None -> (fun ~summary:_ _ _ _ p -> p)
    | Some f -> f in

  let shuffle_refinements ~summary (c1,r1) (c2,r2) (c_out,out_r) ctxt =
    let gen_constraint =
      force_cons || summary
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
    let join_envs c1 c2 =
      assert (List.length c1.env = List.length c2.env);
      assert (List.length c1.nullity_stack = List.length c2.nullity_stack);
      let e1 = List.fast_sort (fun (p1,_,_) (p2,_,_) ->
          Paths.compare p1 p2
        ) c1.env
      in
      let e2 = List.fast_sort (fun (p1,_,_) (p2,_,_) ->
          Paths.compare p1 p2
        ) c2.env
      in
      let merge_nullity =
        (* "IT'S AN N2 --- "
           "REI!!"
        *)
        List.map2 (fun n1 n2 ->
          match n1,n2 with
          | ((`NLive | `NNull) as n),`NVar _
          | (`NVar _),((`NLive | `NNull) as n) -> n
          | `NVar id,`NVar _ -> `NVar id
          | _,_ -> assert (n1 = n2); n1
        )
      in
      (
        merge_nullity c1.nullity_stack c2.nullity_stack,
        close_env @@ List.fold_left2 (fun acc (p1,r1,nl1) (p2,r2,nl2) ->
            assert (p1 = p2);
            (p1,And (r1,r2),(merge_nullity nl1 nl2))::acc
          ) g e1 e2
      )
    in
    if gen_constraint then
      let mk_constraint (nullity,env) ante =
        pp ~summary (c_r1,c1) (c_r2,c2) c1.path @@ {
          env;
          ante;
          conseq = c_out_r;
          nullity;
          target = Some c1.path
        }
      in
      let cons = [
        mk_constraint (join_envs c1 c2) @@ And (c_r1,c_r2);
      ] in
      let (ctxt',d_list) = ctxt in
      ({ ctxt' with refinements =
           cons @ ctxt'.refinements },d_list)
    else begin
      let (i,_) = unsafe_extract_pred c_out_r in
      let comb_pred = And (partial_subst c1.sym_bindings r1, partial_subst c2.sym_bindings r2) in
      let (ctxt',d_list) = ctxt in
      (ctxt',(i,comb_pred)::d_list)
    end
  in
  let next_nvar =
    let counter = mk_counter () in
    fun () ->
      let nxt = counter () in
      nxt * 2
  in

  let rec inner_loop ~summary (c1,t1) (c2,t2) (c_out,out_t) ctxt =
    match t1,t2,out_t with
    | Tuple (b1,tl1), Tuple (b2,tl2), Tuple (b_out,tl_out) ->
      let st1 = step_tup c1 ~b_out b1 tl1 in
      let st2 = step_tup c2 ~b_out b2 tl2 in
      let st3 = step_tup c_out b_out tl_out  in
      fold_left3i (fun c ind t1' t2' t_out' ->
        inner_loop ~summary
          (st1 ind t1')
          (st2 ind t2')
          (st3 ind t_out')
          c
      ) ctxt tl1 tl2 tl_out

    | Ref (t1',_,n1), Ref (t2',_,n2), Ref (t_out',flg,n_out) ->
      if not flg then
        ctxt
      else
        inner_loop ~summary
          (step_ref next_nvar c1 t1' n1)
          (step_ref next_nvar c2 t2' n2)
          (step_ref next_nvar c_out t_out' n_out)
          ctxt

    | TVar _,TVar _,TVar _ ->
      ctxt
        
    | Mu (_,_,_,t1'), Mu (_,_,_,t2'), Mu (_,_,_,out_t') ->
      inner_loop ~summary:true (c1,t1') (c2,t2') (c_out,out_t') ctxt
        
    | Int r1,Int r2,Int out_r ->
      shuffle_refinements ~summary
        (c1,r1)
        (c2,r2)
        (c_out,out_r)
        ctxt
    | Array (b1,len1,_,t1), Array (b2,len2,_,t2), Array (b_out,len_out,flg,t_out) ->
      if not flg then ctxt
      else
        let ctxt' = shuffle_refinements ~summary:true (c1,len1) (c2,len2) (c_out,len_out) ctxt in
        inner_loop ~summary:true
          (step_array c1 b1 len1 t1)
          (step_array c2 b2 len2 t2)
          (step_array c_out b_out len_out t_out)
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
      env = [];
      nullity_stack = [];
      sym_bindings = []
    },t)
  in
  inner_loop ~summary:false
    (mk_ctxt [] t1)
    (mk_ctxt t2_bind t2)
    (mk_ctxt out_bind out_type)
    (ctxt,[])

let rec push_subst bind = function
  | Int r ->
    let sigma = List.map (fun (i,v) -> (i,`Concr (P.var v))) bind in
    Int (partial_subst sigma r)
  | Ref (t,o,n) -> map_ref (push_subst bind) t o n
  | Tuple (b,tl) ->
    let b_ext = List.map (fun (i,v) -> (i,SVar v)) bind in
    Tuple (b_ext @ b, tl)
  | TVar id -> TVar id
  | Mu (i,fv,a,t) -> Mu (i,fv,a,push_subst bind t)
  | Array (b,len_p,o,t) ->
    let sigma = List.map (fun (i,v) -> (i,`Concr (P.var v))) bind in
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
    |> with_type @@ strengthen_eq ~strengthen_type:t ~target:(P.var v)
  | Ref _,_ ->
    (ctxt,t)
  | Array _,PVar v ->
    maybe_strengthen_patt v ctxt
    (* strengthen eq, as a special case, can propagate length equalites *)
    |> with_type @@ strengthen_eq ~strengthen_type:t ~target:(P.var v)
  | Array _,_ ->
    (ctxt,t)
  | Tuple (b,tl),PVar v ->
    let tl' = List.mapi (fun i t ->
        strengthen_eq ~strengthen_type:t ~target:(P.t_ind (P.var v) i)
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
  | _,Nondet _
  | _,Null
  | _,Call _ -> ctxt
  | _,Var v ->
    let t = SM.find v ctxt.gamma in
    let (ctxt',t') = strengthen_type ~root:(P.var v) t patt ctxt in
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
   let t' = strengthen_eq ~strengthen_type:(SM.find lhs ctxt.gamma) ~target:(P.len (P.var arr)) in
   let (b,l,o,et) = lkp_array arr in
   ctxt
   |> update_type lhs t'
   |> update_type arr @@ Array (b,And (l,Relation {
             rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr (P.var lhs))
           }),o,et)
  | _,Deref v ->
    let (t,o,n) = lkp_ref v in
    if o then
      let (ctxt',t') = strengthen_type t patt ctxt in
      update_type v (Ref (t',o,n)) ctxt'
    else
      ctxt
  | (PVar v),Mkref (RVar v') ->
    let (t,o,n) = lkp_ref v in
    let t' = strengthen_eq ~strengthen_type:t ~target:(P.var v') in
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
        let vt' = strengthen_eq ~strengthen_type:v_type ~target:(P.t_ind (P.var v) ind) in
        let e_t' = strengthen_eq ~strengthen_type:e_t ~target:(P.var v') in
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


let rec post_update_type = function
  | Int _ -> false
  | Tuple (_,tl) -> List.exists post_update_type tl
  | Array _
  | Ref _ -> true
  | TVar _ | Mu _ -> failwith "Bare recursive type"

let%lm remove_sub ps ctxt =
  List.fold_left (fun c (i,_) ->
    { c with pred_arity =
        StringMap.remove i c.pred_arity }) ctxt ps

let add_post_type_p pos path =
  (not pos.under_mu) && (not pos.array_ref) && not @@ Paths.is_const_ap path

let constrain_fold  ~unfolded:(unfolded_t,_) ~folded:(folded_t,path) ctxt =
  let folded_unfold = unfold_once folded_t in
  add_type_implication (denote_gamma ctxt.gamma) path unfolded_t folded_unfold ctxt

let simple_type_at id ctxt = 
  IntMap.find id ctxt.iso.SimpleChecker.SideAnalysis.let_types

let get_type_scheme mloc ?(is_null=false) ~loc ~fv id v =
  let%swith st = simple_type_at id in
  lift_to_refinement mloc ~nullity:(if is_null then NNull else NUnk)  ~pred:(fun ~mu ~pos:{under_mu; _} fv p ->
      let%bind p = alloc_pred ~mu ~ground:(under_mu || is_null) ~loc fv p in
      return @@ Pred (p,fv)
  ) (P.var v) fv st

let%lm bind_var v t ctxt =
  { ctxt with gamma = SM.add v t ctxt.gamma }

(* ind_var must be a local variable, and therefore must be in scope *)
let%lm add_bounds_constraint dg arr_var ind_var ctxt =
  let len_ap = RAp (P.len (P.var arr_var)) in
  let ind_ap = RImm (RAp (P.var ind_var)) in
  let index_constr = And (Relation {
        rel_op1 = ind_ap; rel_cond = ">="; rel_op2 = RConst 0
      }, Relation {
        rel_op1 = ind_ap; rel_cond = "<"; rel_op2 = len_ap
      })
  in
  {
    ctxt with
    refinements = {
      env = dg;
      ante = Top;
      conseq = index_constr;
      nullity = [];
      target = None
    }::ctxt.refinements
  }

let propagate_nullity ~src ?(unfold_dst=false) ~dst =
  let null_counter = mk_counter () in
  let rec to_template =
    function
    | Int r -> return @@ Int r
    | TVar id -> return @@ TVar id
    | Mu (a,fv,i,t) ->
      let%bind t' = to_template t in
      return @@ Mu (a,fv,i,t')
    | Tuple (b,tl) ->
      let%bind tl' = mmap to_template tl in
      return @@ Tuple (b,tl')
    | Array (ar,len_r,o,t) ->
      let id = null_counter () in
      let%bind () = mutate @@ IntMap.add id o in
      let%bind t' = to_template t in
      return @@ Array (ar,len_r,id,t')
    | Ref (t,o,_) ->
      let id = null_counter () in
      let%bind () = mutate @@ IntMap.add id o in
      let%bind t' = to_template t in
      return @@ Ref(t',id,())
  in
  let ((o_map : bool IntMap.t),tmpl) = to_template dst IntMap.empty in
  let tmpl_u =
    if unfold_dst then
      unfold_once_gen (unfold_gen ~gen:fresh_tvar  ~rmap:(fun _ r -> r) ~iref:ignore_iref) tmpl
    else
      tmpl
  in
  let store_null id n =
    IntMap.update id (fun s ->
      Option.fold ~none:n ~some:(join_nullity n) s
      |> Option.some
    )
  in
  let rec propagate_loop acc t1 t2 =
    match t1,t2 with
    | TVar _, TVar _
    | Int _,Int _ -> acc
    | Ref (t1',_,n), Ref (t2',id,_) ->
      propagate_loop (store_null id n acc) t1' t2'
    | Array (_,_,_,t1'),Array (_,_,_,t2')
    | Mu (_,_,_,t1'),Mu (_,_,_,t2') ->
      propagate_loop acc t1' t2'
    | Tuple (_,tl1), Tuple (_,tl2) ->
      List.fold_left2 propagate_loop acc tl1 tl2
    | t1_,t2_ -> type_mismatch t1_ t2_
  in
  let nullity_map = propagate_loop IntMap.empty src tmpl_u in
  let rec apply_nullity_loop = 
    function
    | Int r -> Int r
    | Mu (a,b,c,t) -> Mu (a,b,c,apply_nullity_loop t)
    | Array (a,l,id,t) ->
      Array (a,l,IntMap.find id o_map,apply_nullity_loop t)
    | Tuple (b,tl) ->
      Tuple (b,List.map apply_nullity_loop tl)
    | TVar id -> TVar id
    | Ref (t,id,_) ->
      let null = IntMap.find id nullity_map in
      let o = IntMap.find id o_map in
      Ref (apply_nullity_loop t,o,null)
  in
  (apply_nullity_loop tmpl : typ)

(* TODO: thread context through everywhere A LA ownershipInference *)
let rec process_expr ?output ?(remove_scope=SS.empty) ((e_id,_),e) ctxt =
  let lkp_split ?(loc=OI.SBind e_id) v ctxt =
    let t = SM.find v ctxt.gamma in
    let ctxt,(t1,t2) = split_type loc (P.var v) t ctxt in
    (update_type v t1 ctxt),t2
  in
  let lkp v ctxt = SM.find v ctxt.gamma in
  let%lq mlkp v ctxt = lkp v ctxt in
  let lkp_ref v = match%bind mlkp v with
    | Ref (r,o,n) -> return (r,o,n)
    | _ -> failwith "Not actually a ref"
  in
  let lkp_array v = match SM.find v ctxt.gamma with
    | Array (b,l,o,et) ->
      let cmp_l = compile_refinement (P.len (P.var v)) [] l in
      let len_bind = (P.len (P.var v),cmp_l, []) in
      (b,l,o,et,len_bind)
    | _ -> failwith "not an array"
  in
  let%lq maybe_unfold t ({ iso = { unfold_locs; _ }; _ }) =
    if IntSet.mem e_id unfold_locs then
      (unfold_once t)
    else
      t
  in
  ctxt.store_env e_id @@ ctxt.gamma;
  match e with
  | EVar v ->
    do_with_context ctxt @@ begin
      let%bind t2 = lkp_split ~loc:(SRet e_id) v in
      let%bind dg = denote_gamma_m in
      let%bind gamma = Let_syntax.proj ~f:(fun ctxt -> ctxt.gamma) in
      match output with
      | Some (t,out_args) -> 
        add_type_implication dg (P.var v) t2 t
        >> miter (fun (k,ty) ->
          add_var_implication dg gamma k ty
        ) out_args
      | None -> mutate @@ remove_var ~loc:(LLet e_id) remove_scope
    end
  | Seq (e1, e2) ->
    process_expr e1 ctxt
    |> process_expr ?output ~remove_scope e2

  | Assign (lhs,IVar rhs,cont) ->
    do_with_context ctxt @@
      let%bind t2 = lkp_split rhs 
      and (orig,o,_)  = lkp_ref lhs in
      let%bind t2_assign =
        if IntSet.mem e_id ctxt.iso.fold_locs then
          let%bind t2_fresh_prenull = make_fresh_type ~os:(Ownership (OI.MGen e_id)) ~target_var:(P.deref (P.var lhs)) ~fv:(gamma_predicate_vars ctxt.gamma) ~loc:(LFold e_id) orig in
          let t2_fresh = propagate_nullity ~src:t2 ~unfold_dst:true ~dst:t2_fresh_prenull in

          constrain_fold ~folded:(t2_fresh,P.deref (P.var lhs)) ~unfolded:(t2,rhs)
          >> return t2_fresh
        else
          return t2
      in
      let t2_eq = strengthen_eq ~strengthen_type:t2_assign ~target:(P.var rhs) in
      mupdate_type lhs @@ ref_of t2_eq o NLive
      >> mutate @@ process_expr ?output ~remove_scope cont

  | Assign (lhs,IInt i,cont) ->
    let ctxt,(_,o,_) = lkp_ref lhs ctxt in
    ctxt
    |> update_type lhs @@ ref_of (Int (ConstEq i)) o NLive
    |> process_expr ?output ~remove_scope cont

  | Update (base,ind,v,cont) ->
    let (b,l,o,et,lenr_comp) = lkp_array base in
    let elem_ap = P.elem (P.var base) in
    let len_ap = P.len (P.var base) in
    let ind_ap = RAp (P.var ind) in
    let arr_vars = bind_of_arr b (P.var base) in


    do_with_context ctxt @@
      let%bind et' = make_fresh_type ~os:Prev ~target_var:elem_ap ~loc:(LUpdate e_id) ~fv:(gamma_predicate_vars ctxt.gamma @ fv_of_arr b) ~bind:arr_vars et in
      let%bind t1 = lkp_split v in
      let%bind dg = denote_gamma_m in
      let rel_ind_ap = RImm (RAp (P.ind (P.var base))) in

      let update_case_env = lenr_comp::dg in
      let update_bind = [
        b.len, len_ap;
        b.ind, (P.var ind);
      ] in
      let orig_case_env = update_array_env ~nullity:[] dg (P.var base) [] l in
      let orig_case_bind = update_array_bind b (P.var base) [] in
      begin%m
          add_type_implication ~init_bind:update_bind update_case_env (P.var v) t1 et';
           add_type_implication ~init_bind:orig_case_bind ~ante_ext:(Relation { rel_op1 = rel_ind_ap; rel_cond = "!="; rel_op2 = ind_ap }) orig_case_env elem_ap et et';
           add_bounds_constraint (lenr_comp::dg) base ind;
           mupdate_type base @@ Array (b,l,o,et');
           mutate @@ process_expr ?output ~remove_scope cont
      end

  | Let (PVar v,Mkref (RVar v_ref),exp) when IntSet.mem e_id ctxt.iso.fold_locs ->
    (* FOLD, EVERYBODY FOLD *)
    do_with_context ctxt @@
      let%bind fv = predicate_vars_m in
      let%bind fresh_type = get_type_scheme (OI.MGen e_id) ~loc:(LFold e_id) ~fv e_id v in
      let (fresh_cont_prenull,o,_) = unsafe_split_ref fresh_type in
      let%bind t2 = lkp_split v_ref in
      let fresh_cont = propagate_nullity ~src:t2 ~unfold_dst:true ~dst:fresh_cont_prenull in
      let fresh_strengthened = strengthen_eq ~strengthen_type:fresh_cont ~target:(P.var v_ref) in
      begin%m
          constrain_fold ~folded:(fresh_cont,(P.deref (P.var v))) ~unfolded:(t2,v_ref);
           bind_var v @@ ref_of fresh_strengthened o NLive;
           mutate @@ process_expr ?output ~remove_scope:(SS.add v remove_scope) exp
      end
  | Let (PVar lhs,MkArray len,nxt) ->
    do_with_context ctxt @@ begin
      let%bind dg = denote_gamma_m
      and lent = mlkp len
      and fv = predicate_vars_m in
      let%swith st = simple_type_at e_id in
      let%bind a_type =
        lift_to_refinement (OI.MGen e_id) ~nullity:NLive ~pred:(fun ~mu ~pos:{under_ref; under_mu; _} fv path c ->
          match (path : P.path :> P.root * 'b * P.suff) with
          | (P.Var v, [], `Len) when v = lhs ->
            (c,Relation { rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr (P.var len)) })
          | (_, _, `Len) -> unsupported "Nested arrays"
          | _ -> if under_ref || under_mu then
              make_fresh_pred ~mu ~ground:true ~pred_vars:(fv,path) ~loc:(LMkArray e_id) c
            else
              c,ConstEq 0
        ) (P.var lhs) fv st
      in
      begin%m
          add_var_implication dg ctxt.gamma len @@ Int (Relation { rel_op1 = Nu; rel_cond = ">="; rel_op2 = RConst 0 });
           mupdate_type len (map_refinement (fun r ->
               And (r,Relation {rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr (P.len (P.var lhs))) })
             ) lent);
           bind_var lhs a_type;
           mutate @@ process_expr ?output ~remove_scope:(SS.add lhs remove_scope) nxt
      end
    end

  | Let (PVar v,Null,nxt) -> do_with_context ctxt @@ begin
      let%bind t = get_type_scheme (OI.MGen e_id) ~is_null:true ~fv:(gamma_predicate_vars ctxt.gamma) ~loc:(LNull e_id) e_id v in
      bind_var v t
      >> mutate @@ process_expr ?output ~remove_scope:(SS.add v remove_scope) nxt
    end
  | Let (patt,rhs,exp) ->
    do_with_context ctxt @@
      (* whither the null and mkarray forms? They're above, because when
         generating the types, we need a concrete path. This can technically reject programs like let _ = null in ...
         but I'm not going to lose TOO much sleep about that *)
      let%bind assign_type = begin
        match rhs with
        | Var left_v ->
          lkp_split left_v           
        | Const n -> return @@ Int (ConstEq n)

        | Nondet r -> return @@ Int (Option.value ~default:Top r)

        | Call c -> process_call e_id c

        | Null
        | MkArray _ -> assert false

        | Deref ptr ->
          let%bind (target_type,o,_) = lkp_ref ptr in
          let%bind (t_rem,t_res) = split_type (OI.SBind e_id) (P.deref @@ P.var ptr) target_type in
          let%bind tres_unfold = maybe_unfold t_res in
          mupdate_type ptr @@ (ref_of t_rem o NLive)
          >> return tres_unfold

        | Ast.Tuple tl ->
          let%bind res = mmapi (fun i h ->
              let proj_ind = Some (fresh_tvar(), SProj i) in
              match h with
              | RNone -> return (Int Top,proj_ind)
              | RInt n -> return (Int (ConstEq n), proj_ind)
              | RVar v ->
                let%bind t2 = lkp_split ~loc:(OI.SBind e_id) v in
                return (t2, match t2 with Int _ -> proj_ind | _ -> None)
            ) tl
          in
          let ty_list,flag_list_opt = List.split res in
          return @@ Tuple (List.filter_map Fun.id flag_list_opt,ty_list)

        | Read (base,ind) ->
          let%bind dg = denote_gamma_m in
          let (b,lr,_,et,comp_l) = lkp_array base in
          let%bind fv = predicate_vars_m in
          (* TODO: no splitting because, uh, what would that look like? *)
          let%bind res_t = make_fresh_type ~os:Prev ~loc:(LRead e_id) ~target_var:(P.elem (P.var base)) ~fv et in
          let read_bind = [
            (b.ind,P.var ind);
            (b.len,P.len (P.var base))
          ] in
          let impl_env = update_array_env ~nullity:[] dg (P.var base) [] lr in
          add_type_implication impl_env  ~init_bind:read_bind (P.elem (P.var base)) et res_t
          >> add_bounds_constraint (comp_l::dg) base ind
          >> return res_t
        | LengthOf _ ->
          return @@ Int (Relation {rel_op1 = Nu; rel_cond = ">="; rel_op2 = RConst 0 })
        | Mkref init' ->
          match init' with
          | RNone -> return @@ Ref (Int Top,true,NLive)
          | RInt n -> return @@ Ref (Int (ConstEq n),true,NLive)
          | RVar r_var ->
            let%bind t2 = lkp_split r_var in
            return (Ref (t2,true,NLive))
      end in
      map_state (fun x -> (0,x)) >>
      let%bind close_p = assign_patt ~let_id:e_id patt assign_type in
      let bound_vars = collect_bound_vars SS.empty close_p in
      map_state snd >>
      mutate @@ strengthen_let close_p rhs >>
      mutate @@ process_expr ?output ~remove_scope:(SS.union bound_vars remove_scope) exp >>
      return ()

  | Assert (relation,cont) ->
    process_expr ?output ~remove_scope cont @@ {
      ctxt with
      refinements = {
        env = denote_gamma ctxt.gamma;
        ante = Top;
        conseq = (lift_relation relation);
        nullity = []; target = None
      }::ctxt.refinements
    }

  | Alias (v1,src_ap,cont) -> do_with_context ctxt @@

      let loc = LAlias e_id in
      (* get the variable type *)
      let%bind t1 = mlkp v1 in
      (* silly *)
      let ap = lift_src_ap src_ap in
      (* Why are we checking unfold_locs here?
         Great question! Short answer: I can't design APIs.
         Long answer: in the simple checker it is much easier to treat
         dereferences in alias expressions as a read, which then gets
         flagged as an unfold (instead of a write, which is an fold). So we allow
         this strangeness until I inevitably mix this up *)
      let is_fold = IntSet.mem e_id ctxt.iso.unfold_locs in
      let prepare_merge (fv,subst) sub_t =
        let%bind t2_sub' = merge_types ~gloc:(OI.MAlias e_id) ~loc ~path:ap ~bind_seed:(fv,subst) ~unfold_t2:is_fold ~t1:t1 ~t2:sub_t in
        let const_subst = List.filter (fun (_,c) -> Paths.is_const_ap c) subst in
        let force_v1_cons = List.length const_subst <> List.length subst in
        let%bind post_t1 = merge_types ~gloc:(OI.MAlias e_id) ~loc ~path:(P.var v1) ~e1_expl:const_subst ~unfold_t1:is_fold ~t1:sub_t ~t2:t1 in
        return (t2_sub',post_t1,force_v1_cons)
      in
      let merge_tuple_elem path b tl j =
        let (fv,subst) = update_binding path b ([],[]) in
        let env = update_tuple_env ~nullity:[] [] path subst b tl in
        let t2_sub = List.nth tl j in
        let%bind t2_sub',t1',force_cons = prepare_merge (fv,subst) t2_sub in
        return (t2_sub,t2_sub',env,subst,t1',force_cons)
      in
      let%bind t2',t2_sub,t2_sub',env,subst,t1',force_v1_cons =
        match src_ap with
        | AVar v ->
          let%bind t2 = mlkp v in
          let%bind (t2_sub',t1',force_cons) = prepare_merge ([],[]) t2 in
          return @@ (t2_sub',t2,t2_sub',[],[],t1',force_cons)
        | AProj (v,j) -> begin
            match%bind mlkp v with
            | Tuple (b,tl) ->
              let%bind t2_sub,t2_sub',_,subst,t1',force_v1_cons = merge_tuple_elem (P.var v) b tl j in
              return @@ ((Tuple (b,update_nth tl j t2_sub')),t2_sub,t2_sub',[],subst,t1',force_v1_cons)
            | _ -> assert false
          end
        | ADeref v -> begin
            match%bind mlkp v with
            | Ref (t2_sub,o,_) ->
              let%bind t2_sub',t1',force_cons = prepare_merge ([],[]) t2_sub in
              return @@ ((Ref (t2_sub',o,NLive)),t2_sub,t2_sub',[],[],t1',force_cons)
            | _ -> assert false
          end
        | APtrProj (v,j) -> begin
            match%bind mlkp v with
            | Ref (Tuple (b,tl),o,_) ->
              let%bind (t2_sub,t2_sub',env,subst,t1',force_v1_cons) = merge_tuple_elem (P.deref (P.var v)) b tl j in
              let t2' = Ref (Tuple (b,update_nth tl j t2_sub'),o,NLive) in
              return @@ (t2',t2_sub,t2_sub',env,subst,t1',force_v1_cons)
            | _ -> assert false
          end
      in
      (* now t1' and t2' refer to the same sets of free variables: any symbolic variables
         appearing in t1' and t2' are bound by tuple types
         
         Finally, we may have to unfold t2' to generate correct constraints
      *)
      let (t2_constr,t2_constr') = if is_fold then (unfold_once t2_sub,unfold_once t2_sub') else (t2_sub,t2_sub') in
      let app_matrix = apply_matrix ~env_seed:env ~t1 ~t2_bind:subst ~t2:t2_constr in
      let rec up_ap ap t2_base' = match (ap : P.path :> 'a * 'b * 'c) with
        | (P.Var v, [], `None) -> mupdate_type v t2_base'
        | (P.Var _,`Deref::_, `None)
        | (P.Var _,`Proj _::_, `None) ->
          up_ap (P.parent ap) t2_base'
        | _ -> assert false
      in
      let%bind psub2 = app_matrix ~force_cons:is_fold ~out_root:ap ~out_bind:subst ~out_type:t2_constr' in
      let%bind psub1 = app_matrix ~force_cons:force_v1_cons ~out_root:(P.var v1) ~out_type:t1' in
      begin%m
          up_ap ap @@ sub_pdef psub2 t2';
           mupdate_type v1 @@ sub_pdef psub1 t1';
           remove_sub psub1;
           remove_sub psub2;
           mutate @@ process_expr ?output ~remove_scope cont
      end

  | Cond(v,e1,e2) ->
    let add_pc_refinement cond ctxt =
      let curr_ref = lkp v ctxt in
      let branch_refinement = {
        rel_op1 = Nu;
        rel_cond = cond;
        rel_op2 = RConst 0
      } in
      ctxt |>
        update_type v @@ map_refinement (fun r -> And (r,Relation branch_refinement)) curr_ref
    in
    let fv_seed = if SS.mem v remove_scope then [] else [`Concr (P.var v)] in
    process_conditional
      ~fv_seed
      ?output ~remove_scope
      ~tr_path:(add_pc_refinement "=")
      ~fl_path:(add_pc_refinement "!=")
      e_id e1 e2 ctxt

  | NCond (v,e1,e2) ->
    process_conditional
      ?output ~remove_scope
      ~tr_path:(fun ctxt ->
        let (ctxt',t) = make_fresh_type ~os:(Ownership (OI.MGen e_id)) ~ground:true ~target_var:(P.var v) ~loc:(LNull e_id) ~fv:[] (lkp v ctxt) ctxt in
        update_type v (make_null t) ctxt'
      )
      ~fl_path:(fun ctxt ->
        let t = SM.find v ctxt.gamma in
        match t with
        | Ref (t,o,_) -> add_type v (Ref (t,o,NLive)) ctxt
        | _ -> assert false)
      e_id e1 e2 ctxt


and process_conditional ?output ?(fv_seed=[]) ~remove_scope ~tr_path ~fl_path e_id e1 e2 ctxt =
  let ctxt1 = process_expr ?output ~remove_scope e1 @@ tr_path ctxt in
  let ctxt2 = process_expr ?output ~remove_scope e2 @@ fl_path {
        ctxt with
        refinements = ctxt1.refinements;
        v_counter = ctxt1.v_counter;
        pred_arity = ctxt1.pred_arity;
      } in
  let loc = LCond e_id in
  let u_ctxt = { ctxt2 with gamma = SM.empty } in
  if output = None then
    let b1 = SM.bindings ctxt1.gamma in
    let b2 = SM.bindings ctxt2.gamma in
    let dg1 = denote_gamma ctxt1.gamma in
    let dg2 = denote_gamma ctxt2.gamma in
    let subsume_types ~target_var t1 t2 =
      let%bind t' = merge_types ~gloc:(OI.MJoin e_id) ~bind_seed:(fv_seed,[]) ~loc ~path:(P.var target_var) ~t1 ~t2 in

      add_var_type_implication dg1 target_var t1 t'
      >> add_var_type_implication dg2 target_var t2 t'
      >> return t'
    in
    List.fold_left2 (fun ctxt (k1,t1) (k2,t2) ->
      assert (k1 = k2);
      let (ctxt',t) = subsume_types ~target_var:k1 t1 t2 ctxt in
      add_type k1 t ctxt'
    ) u_ctxt b1 b2
  else
    u_ctxt

and process_call e_id c ctxt =
  let arg_bindings = List.map (fun k ->
      (k,SM.find k ctxt.gamma)) c.arg_names
  in
  let inst_fn_type = instantiate_fn_type ~lbl:c.label ~pre_map:(
      Paths.map_root (fun p -> "call!" ^ p)
    ) c.arg_names in
  let input_env = ctxt.gamma |> denote_gamma in
  let callee_type = SM.find c.callee ctxt.theta in
  let symb_in_t = List.map inst_fn_type callee_type.arg_types in
  let symb_out_t : typ list = List.map inst_fn_type callee_type.output_types in
  let in_out_types = List.combine symb_in_t symb_out_t in
  let updated_ctxt = List.fold_left2 (fun acc (k,arg_t) (in_t,out_t) ->
      do_with_context acc @@
        let loc = LCall (c.label,k) in
        let constrain_in t ctxt =
          add_type_implication input_env (P.var k) t in_t ctxt          
        in
        let ap = P.var k in
        let%bind (resid,formal) = split_type (OI.SCall e_id) (P.var k) arg_t in
        (* the (to be) summed type, shape equiv to resid_eq and out_t_eq *)
        let%bind fresh_type = merge_types ~gloc:(OI.MGen e_id) ~fv_filter:(fun p ->
            not @@ Paths.is_pre p
          ) ~loc ~path:ap ~t1:out_t ~t2:arg_t in
        let force_cons = post_update_type arg_t in

        let rec get_pred ap kt =
          match P.tail ap with
          | None -> kt (arg_t,[])
          | Some `Deref -> get_pred (P.parent ap) (function
                            | Ref (t,_,n),l -> kt (t,n::l)
                            | Mu _,_ -> None
                            | _ -> assert false
                            )
          | Some (`Proj j) -> get_pred (P.parent ap) (function
                               | Tuple (_,tl),l -> kt ((List.nth tl j),l)
                               | _ -> assert false
                               )
          | Some `Elem -> get_pred (P.parent ap) (function
                           | Array (_,_,_,t),l -> kt (t,l)
                           | _ -> assert false
                           )
          | Some `Len -> get_pred (P.parent ap) (function
                          (* hack *)
                          | Array (_,lr,_,_),l -> kt (Int lr,l)
                          | _ -> assert false
                          )
          | _ -> assert false
        in

        let close_pre_env ~summary (in_pred,arg_ctxt) _ path (constr : tcon) =
          let pre_types =
            let to_pre = 
              match P.tail path with
              (* not in the env set then *)
              | Some `Deref when not summary -> (path,in_pred,arg_ctxt.nullity_stack)::arg_ctxt.env
              (* this should already be in the nullity stack *)
              | _ -> arg_ctxt.env
            in
            let rectify_nullity nl1 nl2 =
              assert (List.length nl1 = List.length nl2);
              List.map2 (fun nl1 nl2 ->
                match nl1,nl2 with
                | NLive,_ -> `NLive
                | NNull,_ -> `NNull
                | NUnk,`NVar id ->
                  `NVar (id + 1)
                | _ -> assert false (* I think? *)
              ) nl1 nl2
            in
            List.filter_map (fun (p,_,n) ->
              if not @@ Paths.is_array_path p then
                get_pred p (function
                | Int r,l -> Some (compile_refinement p arg_ctxt.binding r,l)
                | _ -> assert false
                )
                |> Option.map (fun (pred,nl) ->
                    let n' = rectify_nullity nl n in
                    (Paths.pre (Paths.map_root (fun s -> "call!" ^ s) p),pred,n')
                  )
              else
                None
            ) to_pre
          in
          { constr with env = constr.env @ pre_types }
        in
        let%bind psub = apply_matrix
            ~pp_constr:close_pre_env
            ~t1:resid
            ~t2:out_t
            ~force_cons
            ~out_root:ap
            ~out_type:fresh_type
        in
        (* now the magic *)
        constrain_in formal
        >> mupdate_type k @@ sub_pdef psub fresh_type
        >> remove_sub psub
        >> return ()
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
    | `Concr ap -> 
      let ap' = Paths.map_root (fun i -> List.assoc i sub_map) ap in
      if (not @@ Paths.is_pre ap') || Option.is_none pre_map then
        `Concr ap'
      else
        `Concr ((Option.get pre_map) ap')
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
  let to_reif_name p = Paths.to_z3_ident @@ P.pre @@ Paths.map_root (fun root -> "reif!" ^ root) p in
  let inst_fn_type = instantiate_fn_type  ~pre_map:(fun ap ->
      P.var (to_reif_name ap)
    ) arg_names in
  let f_typ = SM.find fdef.name ctxt.theta in
  let typ_template = List.combine arg_names f_typ.arg_types in
  let init_env = List.fold_left (fun g (n,t) ->
      let inst = inst_fn_type t in
      let (g',inst') =
        walk_with_path (fun ~pos path p g ->
          if (not (add_post_type_p pos path)) || (is_max_ref pos) then
            (g,p)
          else
            let pre_path = to_reif_name path in
            (SM.add pre_path (Int Top) g, And (p, Relation { rel_op1 = Nu; rel_cond = "="; rel_op2 = RAp (`Concr (P.var pre_path)) }))
            
        ) (P.var n) inst g
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
  let ctxt' = process_expr ~output:(result_type,output_args) ~remove_scope:SS.empty fdef.body { ctxt with gamma = init_env } in
  ctxt'

let process_function ctxt fdef =
  let c = process_function_bind ctxt fdef in
  { c with gamma = SM.empty }

let infer ~save_types ~intrinsics (st,iso) o_hints (fns,main) =
  let init_fun_type f_def =
    let lift_simple_type ~gloc ~post ~loc =
      lift_to_refinement gloc ~nullity:NUnk ~pred:(fun ~mu ~pos fv path ->
        let fv' =
          if (post path) && (add_post_type_p pos path) then
            (`Concr (Paths.pre path))::fv
          else
            fv
        in
        make_fresh_pred ~mu ~ground:pos.under_mu ~pred_vars:(fv',path) ~loc
      )
    in
    let gen_arg_preds ~gloc ~post ~loc fv arg_templ = mmap (fun (k,t) ->
        let fv' = List.filter_map (fun x ->
            match (x : P.path :> P.root * 'a * P.suff) with
            | (P.Var v,[],`None) when v = k -> None
            | _ -> Some (`Concr x)) fv in
        lift_simple_type ~gloc ~post ~loc:(loc k) (P.var k) fv' t
      ) arg_templ
    in
    let simple_ftype = SM.find f_def.name st in
    let symbolic_args = List.mapi (fun i _ -> Printf.sprintf "$%d" i) f_def.args in
    let arg_templ = List.combine symbolic_args simple_ftype.SimpleTypes.arg_types in
    let free_vars =
      List.filter_map (function
      | (k,`Int) -> Some (P.var k)
      | (k, `Array `Int) -> Some (P.len @@ P.var k)
      | _ -> None
      ) arg_templ in
    let%bind arg_types = gen_arg_preds ~gloc:(MArg f_def.name) ~post:(Fun.const false) ~loc:(fun k -> LArg (f_def.name,k)) free_vars arg_templ in
    let post_positions = List.fold_left2 (fun acc symb arg_type ->
        fold_with_bindings (fun ~pos p _ _ set ->
          if not @@ is_max_ref pos then
            P.PathSet.add p set
          else
            set
        ) (P.var symb) empty_bindings arg_type acc
      ) P.PathSet.empty symbolic_args arg_types
    in
    let%bind output_types = gen_arg_preds ~gloc:(MOut f_def.name) ~post:(fun p -> P.PathSet.mem p post_positions) ~loc:(fun k -> LOutput (f_def.name,k)) free_vars arg_templ in
    let%bind result_type =
      lift_simple_type ~gloc:(MRet f_def.name) ~post:(Fun.const false) P.ret ~loc:(LReturn f_def.name) (List.map (fun l -> `Concr l) free_vars) simple_ftype.SimpleTypes.ret_type
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
    refinements = [];
    pred_arity = StringMap.empty;
    v_counter = 0;
    store_env;
    iso;
    o_hints
  } in
  let ctxt = List.fold_left (fun acc fd -> init_fun_type fd acc |> fst) initial_ctxt fns in
  let { refinements; pred_arity; theta; _ } =
    List.fold_left process_function ctxt fns
    |> process_expr main
  in
  Result.{
    refinements;
    theta;
    arity = pred_arity;
    ty_envs 
  }

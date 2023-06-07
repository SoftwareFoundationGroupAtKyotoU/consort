(** 
This module walks the AST of a program, generating a series of ownership constraints (type [ocons]) which encode the
ownership relationships that must hold in any well-typed program.

In addition to the constraints themselves, this analysis produces two major side results: the [ownership_ops] map and
the maximization variables. These are discussed below.
*)

open Ast
open Std
open Std.StateMonad
open Sexplib.Std

module SM = StringMap
module P = Paths

(** An ownership is either a variable, or a constant (between 0.0 and 1.0, incl) *)
type ownership =
    OVar of int (** A variable with id int *)
  | OConst of float (** a constant ownership with the given rational number *)

type ocon =
  | Live of ownership (** The ownership must be greater than 0 (only emitted in relaxed mode) *)
  | Write of ownership (** Constraint ownership variable n to be 1 *)
  | Shuff of (ownership * ownership) * (ownership * ownership) (** ((r1, r2),(r1',r2')) is the shuffling of permissions s.t. r1 + r2 = r1' + r2' *)
  | Split of ownership * (ownership * ownership) (** Split (o,(s,t)) is the constraint that o = s + t *)
  | Eq of ownership * ownership (** o1 = o2 *)
  | Wf of ownership * ownership (** For well-formedness: if o1 = 0, then o2 = 0 *)
  | Ge of ownership * ownership (** o1 >= o2 *)

type 'a otype_ =
  | Array of 'a otype_ * 'a
  | Int
  | Ref of 'a otype_ * 'a
  | Tuple of 'a otype_ list
  | TVar of int
  | IntList of 'a list

type otype = ownership otype_

(** For the most part, the ownership and refinement inference passes may be run independently. The only intersection is
handling 0 ownership references; when a reference drops to 0 ownership, all refinements must go to top (although we use
a different static semantics, see flowInference for details). Thus, we must communicate the refinement inference
step when and where a refinement drops to zero. This is accomplished by way of the ownership_ops map, which records
for each ownership transfer in the program the result ownerships. The [magic_loc] and [split_loc] types defined
below are used for uniquely identify an ownership operation.
*)

(** A type identifying when the ownership inference is asked to synthesize an ownership ex nihilo. Of course,
   the resulting ownership is constrained by future uses of that ownership, but there is no immediate "source"
   of the ownership. The constructor documentation describes where this occurs.
*)
type magic_loc =
  | MGen of int (** When an ownership is created in the context of processing expression with id. Examples include null pointer, computing the result ownership after a call, etc.*)
  | MJoin of int (** Describes the ownership values computed at a control-flow join point. This has to be a separate constructor because an ifnull condition may be the source of two ownerships; the new ownership to assign in the ifnull branch, and the ownerships at the join point. *)
  | MArg of string (** The ownership of an argument to function nm *)
  | MOut of string (** The ownership of the result to function nm *)
  | MRet of string (** The ownership of the return value from nm *)
  | MAlias of int (** The ownership generated at an alias statement with id *) [@@deriving sexp]

(**
   Split loc is for describing when a single, known ownership is split into to components (with the + operator).
*)
type split_loc =
  | SBind of int (** For an assignment occuring at expression with id *)
  | SCall of int (** When splitting an argument passed in to a function at call with expression id *)
  | SRet of int (** When splitting a variable being returned out of a function *)  [@@deriving sexp]

(** These two maps give the results of ownership operations. The result is defined on a pair of the ownership operation (identified
   by a split_loc or magic_loc) and the access path (see Paths) of a reference type. These maps are partial, they do NOT contain any
   information if a reference (identified by a path) was not split or assigned new ownership during an ownership operation *)

(** The second component of the key identifies the reference that was being split by the assignment *)
module SplitMap : Map.S with type key = (split_loc * Paths.concr_ap) = Map.Make(OrderedPair(DefaultOrd(struct type t = split_loc end))(P.PathOrd))
    
(** The second component of the key identifies the reference that was "magically" given a new ownership *)
module GenMap = Map.Make(OrderedPair(DefaultOrd(struct type t = magic_loc end))(P.PathOrd))

type 'a ownership_ops = {
  splits: ('a * 'a) SplitMap.t; (** The codomain of this map gives a pair of ownerships. 
                                   The first element is the ownership REMAINING in the SOURCE reference (as identified by the second
                                   component of the key). The second element is the
                                   ownership TRANSFERRED to the TARGET of the split. *)
  gen: 'a GenMap.t (** The codomain is the new ownership to assign to the reference identified in the second component of the key *)
}

(** The relaxed flag determines how aggressive ConSORT is when
   maximizing ownership preservation.  By default (non-relaxed mode,
   or stressed mode I guess) ConSORT emits a maximization constraint
   to asking to maximize the number of non-zero ownership
   variables. This can lead to an enormous maximization constrain with
   non-linear components.

   As an alternative, we provide the relaxed mode, which is more
   selective in how it maximizes the ownership variables to track.
   This doesn't come without tradeoff; relaxed mode requires that
   dereferenced pointers must have non-zero ownership.
   Intuitively, instead of ensuring invariants have not been
   discarded on referenced pointers through a maximization constraint, we
   encode this requirement directly (at the cost of some theoretical
   loss of typability, but the use cases for reading a 0 ownership reference
   appear limited). Given this constraint, it suffices to ensure the refinement
   information on a variable that is non-zero is not spuriously weakened
   before future write. Spurious weakenings can occur when all of the ownership
   of a reference is transferred to a function parameter, where the parameter's
   refinement is a weakening of the argument refinement. When the result refinement
   is transferred back; we will then lose refinement information. It thus
   suffices to maximize: a) the ownership of the variables representing the residual
   ownership of function arguments after some ownership has been transferred to
   the function parameters, and b) the ownership returned back to the function.
 *) 

type context = {
  relaxed : bool;
  ovars: int list;
  max_vars: Std.IntSet.t; (** This tracks the ownership variables to
                             maximize. In relaxed mode, it is those
                             representing residual argument ownership,
                             in regular mode, it is all ownership
                             variables. *)
  v_counter: int;
  iso: SimpleChecker.SideAnalysis.results;
  ocons: ocon list;
  gamma: otype StringMap.t;
  theta: (otype RefinementTypes._funtype) StringMap.t;
  op_record: ownership ownership_ops;
  save_env: otype StringMap.t IntMap.t (** Save the ownership types at
                                          each point in the program;
                                          only used for debugging *)
}

type infr_options = bool

let infr_opts_default = false

(* let unfold =
  let rec subst_once id sub = function
    | TVar id' when id = id' -> sub
    | (Int as t)
    | (TVar _ as t) -> t
    | Ref (t,o) -> Ref (subst_once id sub t,o)
    | Array (t,o) -> Array (subst_once id sub t,o)
    | Tuple tl -> Tuple (List.map (subst_once id sub) tl)
    | Mu (id',t) -> assert (id' <> id); Mu (id',subst_once id sub t)
    | IntList -> assert false
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
    | IntList -> assert false
  in
  unfold_loop ~unfld:IntSet.empty *)

(** The optional relaxed argument indicates whether the passed in
   constraint should be applied only if the relaxed flag is in the indicated state.
   otherwise the constraint is added unconditionally.*)
(* N.B. the lm extension, see the README and the StateMonad for an explanation *)
let%lm add_constraint ?relaxed c ctxt =
  match relaxed with
  | Some b when ctxt.relaxed = b ->
    { ctxt with ocons = c::ctxt.ocons }
  | None -> { ctxt with ocons = c::ctxt.ocons }
  | _ -> ctxt

(** Shuffle the ownership between two source types (t1 and t2) and two destination
   types (t1' and t2'). The two types must be iso-recursively equal; they are walked in
   parallel, at references the ownerships are shuffled with the Shuff constraint. *)
let%lm shuffle_types (*~e_id*) ~src:(t1,t1') ~dst:(t2,t2') ctxt =
  (* check whether we need to unfold the "destination", which in this case is t2/t2', not t1/t1'.
     This confusing naming arises from this functions use in returning ownership to a recursive
     data structure, in that case, t2/t2' represents the destination for the return operation. *)
  let unfold_dst =
    (* if IntSet.mem e_id ctxt.iso.SimpleChecker.SideAnalysis.unfold_locs then
      unfold
    else *)
      Fun.id
  in
  let rec loop t1 t2 t1' t2' ctxt =
    match t1,t2,t1',t2' with
    | Int,Int,Int,Int -> ctxt
    | Array (r1,o1), Array (r2,o2), Array (r1',o1'), Array (r2',o2')
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

(** Like shuffle above, but no unfolding occurs, and the destination type [out] must
   have an ownership equal to the "pointwise" sum of ownerships in [t1] and [t2]. *)
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
  | `IntList -> assert false

(** Walk a type, constraining the first occurrence of an
   ownership variable to be well-formed w.r.t [o]. 
   Recall well-formedness requires that if o = 0 => o' = 0
   for the "child" ownership o'. *)
let rec constrain_wf_loop o t ctxt =
  match t with
  | TVar _
  | Int
  | IntList _ -> (ctxt,())
  | Tuple tl ->
    miter (constrain_wf_loop o) tl ctxt
  | Ref (t',o')
  | Array (t',o') ->
    constrain_wf_loop o' t' {
        ctxt with ocons = Wf (o,o')::ctxt.ocons
      }

(** Like constrain_wf_above, but only begin emitting wf constraints
   when the first ownership variable is encountered *)
let rec constrain_well_formed = function
  | TVar _
  | Int -> return ()
  | Tuple tl -> miter constrain_well_formed tl
  | Mu (_,t) -> constrain_well_formed t
  | Ref (t,o)
  | Array (t,o) -> constrain_wf_loop o t
  | IntList -> assert false

(** Record the allocation of an ownership variable in the context
   of a magic operation. Updates the gen map *)
let%lm record_alloc loc p o ctxt =
  let op = ctxt.op_record in
  {
    ctxt with op_record = {
      op with
      gen = GenMap.add (loc,p) o op.gen
    }
  }

(** Record the splitting of the ownership of a reference
at path [p] in the context of a ownership operation [loc].
   The resulting ownerships, [o1] and [o2] are recorded in the split map *)
let%lm record_split loc p o1 o2 ctxt =
  let op = ctxt.op_record in
  { ctxt with op_record = {
      op with splits = SplitMap.add (loc,p) (o1,o2) op.splits
    }
  }

(** Functions to allocating ownership variables to handle splits/generations;
   instrumented to record using the functions above. [alloc_ovar] is to generate
   a fresh ownership variable (always??? in the context of a generation op) and
   alloc_split generates two ownership variables in the context of a split operation. *)
let alloc_split,alloc_ovar =
  let alloc_ovar_inner ctxt =
    let new_ovar = ctxt.v_counter in
    let max_vars =
      if ctxt.relaxed then
        ctxt.max_vars
      else
        (* In "stressed" mode, all variables are max *)
        Std.IntSet.add new_ovar ctxt.max_vars
    in
    { ctxt with
      ovars = new_ovar::ctxt.ovars;
      v_counter = ctxt.v_counter + 1; max_vars },OVar ctxt.v_counter
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

(** Lift a simple type into an ownership type (of type otype) *)
(* this must record *)
let lift_to_ownership loc root t_simp ~o_arity =
  let rec lift_list_to_ownership loc root ~o_arity =
    if o_arity <= 0 then return []
      else (
        let%bind o = alloc_ovar loc root in
        let%bind o_list = lift_list_to_ownership loc root ~o_arity:(o_arity - 1) in
        return (o :: o_list)
      )
  in
  let rec simple_lift ~unfld root =
    function
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
    | `IntList ->
      let%bind o_list = lift_list_to_ownership loc root ~o_arity in
      return @@ IntList o_list
  in
  let%bind t = simple_lift ~unfld:IntSet.empty root t_simp in
  constrain_well_formed t >> return t

let mtmap p f tl =
  mmapi (fun i e -> f (P.t_ind p i) e) tl

(** Make a fresh type of the same shape as [t], whose
   root is at the path [root]. The ownership variables
   attached to references reachable from [root]
   allocated are done so in magic context [loc] *)
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
  | IntList -> assert false
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

(** Map the type bound to v according to continuation k. k
   is stateful function (aka a monadic operation) which
   returns a 3-ary tuple. The first element is the new type for
   for v. The second two components are returned to the caller.
   The new type for v is not immediately applied, rather the returned tuple
   includes a monadic update that, when applied, performs the update to
   the new type.
*)
let map_type k v  =
  let%bind t = lkp v in
  let%bind (t',subt,subt') = k t in
  return @@ (update_type v t',subt,subt')

(**
   Allocates a fresh type for the reference rooted at path [p]. This
   function returns a 3-ary tuple consisting of:
   1. a monadic update, which applies the update at [p] to the environment
   2. the original type at [p]
   3. The fresh type at [p]
*)
let fresh_ap e_id (p: P.concr_ap) =
  let loc = MAlias e_id in
  let (root,steps,suff) = (p :> P.root * P.steps list * P.suff) in
  let v =
    match root,suff with
    | Var v,`None -> v
    | _ -> assert false
  in
  let rec loop (k: ?o:ownership -> _) st =
    match st with
    | [] -> map_type (fun t -> k t) v
    | `Deref::l ->
      loop (fun ?o:_ in_t ->
          match in_t with
          | Ref (in_t',o) ->
            let%bind (new_t,lt,lt') = k ~o in_t' in
            return @@ (Ref (new_t,o), lt, lt')
          | _ -> assert false
        ) l
    | `Proj i::l ->
      loop (fun ?o in_t ->
          match in_t with
          | Tuple tl ->
            let ith = List.nth tl i in
            let%bind (new_sub,lt, lt') = k ?o ith in
            let tl' = update_nth tl i new_sub in
            return @@ (Tuple tl',lt, lt')
          | _ -> assert false
        ) l
  in
  loop (fun ?o t ->
    let%bind t' = make_fresh_type loc p t in
    let%bind () =
      match o with
      | None -> return ()
      | Some o -> constrain_wf_loop o t'
    in
    return (t',t,t')
  ) steps
    
(* this must record *)
let get_type_scheme (*e_id v ctxt*) =
  assert false
  (* let st = IntMap.find e_id ctxt.iso.SimpleChecker.SideAnalysis.let_types in
  lift_to_ownership (MGen e_id) (P.var v) st ctxt *)

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
  | (TVar _ as t)
  | (IntList _ as t) -> return (t,t)
  | Tuple tl ->
    let%bind split_list = mtmap p (split_type loc) tl in
    let (tl1,tl2) = List.split split_list in
    return @@ (Tuple tl1,Tuple tl2)
  | Ref (t,o) -> split_mem o t P.deref tref
  | Array (t,o) -> split_mem o t P.elem tarray


(** Constrain to types to be pointwse constrained by the generator rel, which
   takes two ownerships and returns a constraint *)
let%lm constrain_rel (*~e_id*) ~rel ~src:t1 ~dst:t2 ctxt =
  let dst_unfld =
    (* let open SimpleChecker.SideAnalysis in
    if (IntSet.mem e_id ctxt.iso.unfold_locs) ||
       (IntSet.mem e_id ctxt.iso.fold_locs) then
      unfold t2
    else *)
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

let with_types bindings cont ctxt =
  let (ctxt',fl) = cont {
      ctxt with gamma =
        List.fold_left (fun acc (k,t) ->
          SM.add k t acc
        ) ctxt.gamma bindings }
  in
  { ctxt' with gamma = List.fold_left (fun acc (k,_) ->
        SM.remove k acc
      ) ctxt'.gamma bindings },fl

let lkp_split loc v =
  let%bind t = lkp v in
  let%bind (t1,t2) = split_type loc (P.var v) t in
  update_type v t1 >> return t2

(* let%lq is_unfold eid ctxt =
  let open SimpleChecker.SideAnalysis in
  IntSet.mem eid ctxt.iso.unfold_locs *)

let%lq theta f ctxt = SM.find f ctxt.theta

(** Functionally quite similar to split type, but rather than splitting a type
   in place and giving the two result types, constrains t1 and t2 to be the result
   of splitting out *)
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

let%lm max_ovar ov ctxt =
  match ov with
  | OVar i -> { ctxt with max_vars = IntSet.add i ctxt.max_vars }
  | _ -> ctxt

let rec max_type = function
  | Array (_,o) -> max_ovar o
  | Int | TVar _ -> return ()
  | Mu (_,t) -> max_type t
  | Tuple tl ->
    miter max_type tl
  | Ref (t,o) ->
    max_ovar o >> max_type t
  | IntList -> assert false

let process_call e_id c =
  let%bind arg_types = mmap (lkp_split @@ SCall e_id) c.arg_names
  and fun_type = theta c.callee in
  begin%m
      miter (fun (i,a) -> constrain_eq (*~e_id*) ~src:i ~dst:a) @@ List.combine arg_types fun_type.arg_types;
       miteri (fun i arg_name ->
         let%bind t = lkp arg_name in
         let%bind t' = make_fresh_type (MGen e_id) (P.var arg_name) t in
         let out_type = List.nth fun_type.output_types i in
         (* explicitly flag the residual type as one to maximize *)
         max_type t >>
         sum_types t out_type t' >> update_type arg_name t'
       ) c.arg_names;
       return fun_type.result_type
  end

let%lm save_type e_id ctxt =
  { ctxt with save_env = IntMap.add e_id ctxt.gamma ctxt.save_env }

let rec process_expr ~output ((e_id,_),expr) =
  save_type e_id >>
  match expr with
  | Fail ->
    return `Return
  | Return v ->
    let () = assert (output <> None) in
    let (output_types, return_type) = Option.get output in
    let%bind t2 = lkp_split (SRet e_id) v in
    constrain_eq (*~e_id*) ~src:t2 ~dst:return_type
    >> miter (fun (v,out_t) ->
        let%bind curr_t = lkp v in
        constrain_eq (*~e_id*) ~src:curr_t ~dst:out_t
      ) output_types
    >> return `Return
  | Unit -> return `Cont
  | Seq (e1,e2) ->
    let%bind stat = process_expr ~output e1 in
    assert (stat <> `Return);
    process_expr ~output e2
  | NCond (v,e1,e2) ->
    process_conditional ~e_id ~tr_branch:(
        let%bind t = lkp v in
        let%bind t' = make_fresh_type (MGen e_id) (P.var v) t in
        update_type v t'
      ) ~output e1 e2
  | Cond (_,e1,e2) ->
    process_conditional ~e_id ~tr_branch:(return ()) ~output e1 e2
  | Assign (v,IInt _,nxt) ->
    let%bind (t,o) = lkp_ref v in
    assert (t = Int);
    constrain_write o >> process_expr ~output nxt
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
         constrain_eq (*~e_id*) ~src:t2 ~dst:vt';
         update_type v @@ Ref (vt',o');
         constrain_write o;
         constrain_write o';
         process_expr ~output nxt
    end
  | Update (base,_,contents,nxt) ->
    let%bind (cts,o) = lkp_array base
    and new_cts = lkp_split (SBind e_id) contents in
    begin%m
         constrain_wf_loop o new_cts;
         constrain_write o;
         constrain_eq (*~e_id*) ~src:cts ~dst:new_cts;
         update_type base @@ Array (new_cts,o);
         process_expr ~output nxt
    end
  | Alias(src,dst,nxt) ->
    let%bind (src_up,st,st') = fresh_ap e_id src
    and (dst_up,dt,dt') = fresh_ap e_id dst in
    begin%m
        shuffle_types (*~e_id*) ~src:(st,st') ~dst:(dt,dt');
         src_up;
         dst_up;
         process_expr ~output nxt
    end
  | Assert (_,nxt) -> process_expr ~output nxt
  | Let (PVar v,Mkref (RVar src),body) ->
    let%bind t2 = lkp_split (SBind e_id) src in
    begin
      match%bind get_type_scheme (*e_id v*) with
      | (Ref (ref_cont,o)) as t' ->
        begin%m
            constrain_eq (*~e_id*) ~src:t2 ~dst:ref_cont;
             add_constraint @@ Write o;
             with_types [(v,t')] @@ process_expr ~output body
        end
      | _ -> assert false
    end
  | Let (PVar v,(Null | MkArray _),body) ->
    let%bind t = get_type_scheme (*e_id v*) in
    with_types [(v,t)] @@ process_expr ~output body
  | Let (PVar v,Mkref (RNone | RInt _), body) ->
    let%bind new_var = alloc_ovar (MGen e_id) (P.var v) in
    begin%m
        add_constraint @@ Write new_var;
         with_types [(v,Ref (Int, new_var))] @@ process_expr ~output body
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
        (* let%bind uf = is_unfold e_id in *)
        let t2 =
          (* if uf then
            unfold t2_pre
          else *)
            t2_pre
        in
        begin%m
            update_type v @@ Ref (t1,o);
             (* only require the ownership to be non-zero in relaxed mode (the relaxed argument) *)
             add_constraint ~relaxed:true @@ Live o;
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
      | Cons _
      | Nil -> return IntList
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
    with_types bindings @@ process_expr ~output body
  | Match (_, _, _, _, _) -> assert false
and process_conditional ~e_id ~tr_branch ~output e1 e2 ctxt =
  let (ctxt_tpre,()) = tr_branch ctxt in
  let (ctxt_t,tfl) = process_expr ~output e1 ctxt_tpre in
  let (ctxt_f,ffl) = process_expr ~output e2 { ctxt_t with gamma = ctxt.gamma } in
  match tfl,ffl with
  | `Return,f -> ctxt_f,f
  | `Cont,`Return -> { ctxt_f with gamma = ctxt_t.gamma },`Cont
  | `Cont,`Cont -> 
    let ctxt,() = miter (fun (k,ft) ->
        let%bind t' = make_fresh_type (MJoin e_id) (P.var k) ft in
        let tt = StringMap.find k ctxt_t.gamma in
        let constrain_ge = constrain_rel ~rel:(fun o1 o2 -> Ge (o1, o2)) in
        begin%m
            (* notice that we allow ownership to be discarded at join points, the reason for MJoin *)
            constrain_ge (*~e_id*) ~src:tt ~dst:t';
             constrain_ge (*~e_id*) ~src:ft ~dst:t';
             update_type k t'
        end
      ) (StringMap.bindings ctxt_f.gamma) { ctxt_f with gamma = StringMap.empty } in
    ctxt,`Cont

module Result = struct
  type t = {
    ocons: ocon list;
    ovars: int list;
    op_record: ownership ownership_ops;
    ty_envs: otype StringMap.t IntMap.t;
    theta : (otype RefinementTypes._funtype) StringMap.t;
    max_vars: IntSet.t
  }
end

let analyze_fn ctxt fn =
  let arg_names = fn.args in
  let fn_type = SM.find fn.name ctxt.theta in
  let start_gamma = SM.of_bindings @@ List.combine arg_names fn_type.arg_types in
  let out_type = List.combine arg_names fn_type.output_types in
  let ctxt = List.fold_left (fun ctxt ty -> fst @@ max_type ty ctxt) ctxt fn_type.output_types in
  let (ctxt,_) = process_expr ~output:(Some (out_type,fn_type.result_type)) fn.body { ctxt with gamma = start_gamma } in
  { ctxt with gamma = SM.empty }

let infer ~opts (simple_types,iso) (fn,prog) =
  let lift_plist loc l =
    mmapi (fun i t ->
      lift_to_ownership loc (P.arg i) t ~o_arity:opts.ArgOptions.ownership_arity
    ) l
  in
  let lift_simple_ft nm ft =
    let%bind arg_types = lift_plist (MArg nm) ft.SimpleTypes.arg_types
    and output_types = lift_plist (MOut nm) ft.SimpleTypes.arg_types
    and result_type = lift_to_ownership (MRet nm) P.ret ft.SimpleTypes.ret_type ~o_arity:opts.ArgOptions.ownership_arity in
    return RefinementTypes.{ arg_types; output_types; result_type }
  in
  let rec lift_reft loc p =
    let module R = RefinementTypes in
    function
    | R.Int _ -> return Int
    | R.Tuple tl ->
      let%bind tl' = mtmap p (lift_reft loc) tl in
      return @@ Tuple tl'
    | R.Ref (t,o,_) ->
      let%bind t' = lift_reft loc p t in
      return @@ Ref (t', OConst o)
    | R.Array (_,o,t) ->
      let%bind t' = lift_reft loc p t in
      return @@ Array (t', OConst o)
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
    relaxed = opts.ArgOptions.relaxed_max;
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
    save_env = IntMap.empty;
    max_vars = IntSet.empty
  } in
  let ctxt =
    SM.fold (fun nm st acc ->
      let (acc,ft) = lift_simple_ft nm st acc in
      { acc with theta = SM.add nm ft acc.theta }
    ) simple_types init_context
    |> SM.fold (fun nm it acc ->
        let (acc,ft) = lift_intrinsic_type nm it acc in
        { acc with theta = SM.add nm ft acc.theta }
      ) (ArgOptions.get_intr opts).op_interp
  in
  let ctxt = List.fold_left analyze_fn ctxt fn in
  let (ctxt,_) = process_expr ~output:None prog ctxt in
  {
    Result.ocons = ctxt.ocons;
    Result.ovars = ctxt.ovars;
    Result.op_record = ctxt.op_record;
    Result.ty_envs = ctxt.save_env;
    Result.theta = ctxt.theta;
    Result.max_vars = ctxt.max_vars
  }

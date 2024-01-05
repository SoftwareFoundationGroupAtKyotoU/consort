(**
   The "refinement" inference. Strictly speaking, we are not actually inferring refinements
   on individual variables (that was the purview of the now deleted inference.ml). Instead we are
   inferring relations that summarize the entire program state at each program point (with some extra
   relations for recursive types, explained later).

   We call this module "flowInference" because our encoding gives a symbolic description of the flow
   states (as abstracted by the relations) through the program.

   For the rest of this file to make any sense, you need to understand the following key concepts.

   {3 Relations}
   Ignoring for the moment the handling of recursive types and how to encode null pointers, the set of possible
   states at each program point p is characterized by a relation Rp(...). The arguments to this relation
   are the values of all integer values "reachable" from the current state. In the simplest case, we would characterize
   a state with integer variables x and y with the predicate Rp(x, y). Intuitively, a state is where x takes value v1 and
   y takes value v2 is feasible if Rp(v1, v2). We encode the transformation of states by implications between these
   relations, i.e., suppose we are in a state at p with integer x, and we bind y to x + 1 for the state at p', then we would
   generate the implication Rp(x) => Rp'(x, x + 1), i.e., if we can reach p in a state where x takes value v, then we can
   reach p' in a state where y has value v + 1. So far, so hoare.

   Leaving aside the question of null pointer (see below) references are just another integer value. Assuming no recursive types (again, see below),
   we can easily enumerate the set of symbolic names (expressed as access paths) for every integer value stored in memory (NB: Lacking
   recursive types every reference type must eventually "bottom out" at some integer, and as we don't refine memory locations, we characterize
   our states entirely by the contents of references. Put another way, we don't distinguish between a state where x contains an address a which
   points to 3 vs. a state where x contains an address a' which also points to 3; in both cases, x ultimately points to a value 3.) So, extending
   our example from above, suppose we bound y to mkref x + 1; the implication actually remains the same, but the formal definition of Rp' would
   be R( x, y->* ) indicating the latter integer is stored in a memory cell pointed to by y.

   Leaving aside the complicating factors of havocing, null pointers, and recursive types (though their complexity should not be understated),
   at its core the encoding is quite simple: compute which values from one state can flow to another, and set up an implication from Rp to Rp'
   reflecting these flows (see, e.g., compute_flows).

   {3 Null Handling}
   Null pointers complicate the above simple view of values; sometimes y may not actually hold a value; what should we provide as the second
   argument of Rp' in the above? One possible idea is to pick some arbitrary value held in every null pointer, say 0. This is sound, albeit
   imprecise. For one, the following program is, technically speaking, safe: [let y = null in assert( *y = 1)] (The assertion is never actually
   violated because the program aborts with a NPE first.) However, our naive semantics above will spuriously state the assertion fails because *y is 0.

   A more subtle issue is handling when pointers may be null conditionally (this is often the case with recursive data structures). Suppose we want
   to maintain the invariant that x > 0 is always less than the contents of some (possibly null) reference y. However, if we model y's nullness
   with the dummy value 0, Z3 will conclude that it is not the case x < *y, which may prevent verification.

   The issue lies that any refinement that mentions the contents of a reference must be qualified with "if the containing reference is not null, then...".
   To restate our desired condition from the above paragraph, we should say more precisely that: for some x > 0, if y is non-null, then x < *y.
   But this does not characterize the states where y is null. In that case, x should have no relationship with the contents of y (because, strictly
   speaking, there are none.)

   This case-splitting on the nullity of y gives the intuition for how we handle nullity. For every reference at path p,
   we generate a nullity flag, denoted p?null. This is one of many "shadow state" variables that we introduce. In this case, this
   flag corresponds to the (maybe implicit) runtime tag maintained by the runtime for each reference indicating whether it is null.
   The object language exposes access to this flag with the ifnull, but it is otherwise inaccessible. However, we explicitly model
   it in our static semantics.

   The nullity flag is just another value; flowing along with integers when pointers are assigned or moved. However, they are treated
   specially at certain operations. First, when a reference r is definitely null in some state p, the flag r?null is set to true,
   all null flags reachable from r are set to true, and _all integer values reachable from r are havoced_. When we say havoc, we mean
   the integer values contained within the pointer are left unconstrained, meaning Z3 or another solver may assume they may take any value.
   A reference can definitively proved to be null at assignments of the null pointer constant and the true branch of an ifnull statement.
   For example, if y has simple type int ref in e, we model the binding [let y = null in e], we omit the constraint Rp(...) => Rp'(..., true, * ), where
   * represents a nondeterministic value and Rp' has the arguments of Rp extended with y->* and y?null.

   Dually, as a precondition, we can constrain the null flag to be false when we know the reference must be non-null.
   This is the case when a pointer is either read
   or written, the null flag of the read/written reference may be assumed false, because the operation will fail if the pointer is null.

   Returning to our example [let y = null in assert( *y = 1)], after desugaring we have [let y = null in let t = *y in assert(t = 0)]. The
   The set of states that reach [let t = *y in ...] are characterized by Rp( true, * ). Using the insight described above, we have the
   states of the body of the second let are described by Rp'( y?null, y->*, t) where Rp( false, y->* ) => Rp'( false, y->*, y->* ). However
   There is no state which satisfies the precondition on Rp (the pointer must be null after all), and thus no state reaches Rp', and by extension, the
   (incorrect) assertion.

   {3 Havocing}
   The eagle-eyed will notice that given the definition described so far, Z3 may infer relationships between immutable variables and reference contents,
   treating the reference contents as mutable variables. However, due to aliasing, an update through one reference may update the values
   of multiple static names. This is where ownership, and _havocing_ comes in to play. Recall that for a write to a reference, the ownership
   of all aliasies must be 0. The flowInference module tracks the set of access paths that occur under 0 ownership references. At each write, the
   set of all havoced paths are havoced. Further, whenever reference's ownership drops to zero, the contents of that reference are havoced.
   As with the null pointers above, havocing refers to leaving the value of an access path totally unconstrained, i.e., Z3 or another
   solver may assume it takes any value.

   Intuitively, this havocing corresponds to what the Top refinement indicates; we know the simple type of the access path but
   no further information about its contents. Notice too that this constrains the type of inferences solvers may draw about the relationship
   between immutable storage and mutable cells. For example, suppose the solver concludes y = x->* at some point.
   Then, after an assignment, the ownership of x drops to zero, whereby its contents are havoced. The solver must then conclude that y and x->*
   are not necessarily equal. This conclusion is correct; if x has zero ownership, the memory cell it points to may be written to through
   and alias, so our inference about y = x->* should no longer be assume valid. A non-trivial portion of the inference infrastructure is devoted
   to tracking which paths are havoced when, and ensuring they are havoced correctly.

   {4 Mu Relations and Recursive Types}
   See the documentation for RecRelations and RecursiveRefinements.
*)

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

type z3_types = ZBool | ZInt [@@deriving sexp]

(** An explanatory value explaining what a relation describes. The AliasUnfold relation is explained in the Alias case, and the ExprMu case is used to describe a mu relation *)
type relation_source =
  | Expr of int
  | Fun of string * [ `In | `Out ]
  | FunMu of string * [ `In | `Out ] * P.concr_ap
  | ExprMu of int * P.concr_ap * [ `Null | `Join | `Flow ]
  | AliasUnfold of int
  | Start
[@@deriving sexp]

(** Describes the flows from a source state to the output state. Compiled into substitutions on relation arguments *)
type flow =
  | Havoc of P.concr_ap
      (** Havoc (i.e., make non-deterministic) the value at thegiven path *)
  | Copy of P.concr_ap * P.concr_ap
      (** copy the value from the first path to the second *)
  | Const of P.concr_ap * int  (** Set the value at path p to the constant i *)
  | NullConst of P.concr_ap * bool
      (** The value at the null path p to the null flag constant b *)

type relation = string * (P.concr_ap * z3_types) list * relation_source
[@@deriving sexp]
(** A relation, which may describe the entirety of the program state at a program point, or a recursive relationship.
   The first element is a unique name for the relation, the third element gives the arguments names and types, and the third
   is for debugging cex generation purposes.
 *)

(** Possible values to substitute for arguments to a relation *)
type concr_arg =
  | Ap of P.concr_ap  (** Another symbolic path name *)
  | BConst of bool  (** A boolean constant *)
  | IConst of int  (** integer constant *)
  | KeyedChoice of P.concr_ap * concr_arg * concr_arg
      (** An ite expression which gives a1 if p is true, a2 other wise *)
[@@deriving sexp]

(** Formulae that appear as the components of a CHC *)
type clause =
  | PRelation of relation * (P.concr_ap * concr_arg) list * int option
      (** An application of the given relation, with a substitution described by the second argument, and an option context shift given by the third *)
  | Relation of (concr_arg, concr_arg) RT.relation * z3_types
      (** A logical relation (as described in refinement types) between two concrete arguments of type (z3_types) *)
  | NamedRel of string * concr_arg list
      (** A named relation with the given arguments. Generated by intrinsics; the smt function name is assumed to be built in or defined in the smt definition file for instrinsics *)
  | NullCons of concr_arg * concr_arg
      (** A null "well-formedness" condition, i.e., if the null flag indicated by p1 is true, then the null flag p2 must be true as well (i.e., null pointers cannot point to null pointers *)

type fltype =
  [ `IntArray
  | `Ref of bool * fltype
    (** The boolean flag here indicates whether this reference was under a mu binder which has since been unfolded *)
  | `Int
  | `Tuple of fltype list
  | `Mu of fltype
  | `TVar
  | `Lock of fltype SM.t
  | `ThreadID of fltype SM.t ]

let rec fltype_to_string = function
  | `IntArray -> "[int]"
  | `Mu t ->
      Printf.sprintf "(%s %s.%s)" Greek.mu Greek.alpha @@ fltype_to_string t
  | `Ref (_, t) -> Printf.sprintf "%s ref" @@ fltype_to_string t
  | `Int -> "int"
  | `Tuple tl ->
      Printf.sprintf "(%s)" @@ String.concat ", "
      @@ List.map fltype_to_string tl
  | `TVar -> Greek.alpha
  | `Lock pte -> Printf.sprintf "(%s) lock" @@ pte_to_string pte
  | `ThreadID pte -> Printf.sprintf "(%s) tid" @@ pte_to_string pte

and pte_to_string pte =
  let l =
    StringMap.fold (fun v t l -> (v ^ ": " ^ fltype_to_string t) :: l) pte []
  in
  String.concat ", " l

type funtype = fltype _funtyp

type recursive_ref_map = relation P.PathMap.t
(** A map from from a mu binder path to a recursive mu relation, which describes the recursive relationship that holds between the
    values under the binder, and all values reachable by unfolding the recursive type (see above) *)

type function_info = {
  in_rel : relation;  (** The relation describe pre-states (or preconditions) *)
  out_rel : relation;  (** The out state, which includes the return type *)
  f_type : funtype;
  in_recursive_rel : recursive_ref_map;
      (** The map from mu binders in the arguments to mu relations *)
  out_recursive_rel : recursive_ref_map;  (** The same, but for output results *)
}

type state_snapshot = {
  mu_relations : recursive_ref_map;
  gamma : (string * fltype) list;
  relation : relation;
}

module StringPairMap = Map.Make (struct
  type t = string * string

  let compare = compare
end)

module SPM = StringPairMap

type ctxt = {
  null_checks : bool;
      (** whether to emit checks that all read/written pointers are provably null *)
  relations : relation list;  (** List of all defined relations *)
  impl : (clause list * clause) list;
      (** List of CHC implications, represented by a list of preconditions (clauses) and a single conclusion (a clause) *)
  o_hints : float OI.ownership_ops;
  fenv : function_info SM.t;
  curr_fun : string option;
  let_types : fltype IntMap.t;
  bif_types : RefinementTypes.funtype SM.t;
  havoc_set : P.PathSet.t;
      (** Havoc set is the set of havoced access paths, i.e., the set of access paths under a 0 ownership pointer.
                              We track this explicitly because we must re-havoc these paths on each assignment. If we did not, the following
                              program would (incorrectly) type check: [let x = ... in let y = x in let t = *x in y := 4; assert(t = *x)] *)
  unfold_iso : IntSet.t;
  fold_iso : IntSet.t;
  recursive_rel : recursive_ref_map;
      (** The set of mu relations at each mu binder *)
  snapshots : state_snapshot IntMap.t;
  omit_set : P.PathSet.t StringMap.t;
      (** Mapping from relation names to paths sets.
          The set is the one of the paths which will be not used as arguments of the given relation.
          Used in relaxed mode. *)
  pte_rel : relation SPM.t;  (** Mapping from variables to PTE relations *)
  fn_params : string list StringMap.t;
      (** Mapping from function names to their parameters *)
}

type res_t =
  relation list (* the list of all relations generated *)
  * (clause list * clause) list (* implications *)
  * state_snapshot Std.IntMap.t
  (* snapshots at each location (for annotation) *)
  * string (* entry point relation *)
  * P.PathSet.t StringMap.t (* omit sets (used in relax mode only) *)

let rec unfold_fltype subst : fltype -> fltype = function
  | `TVar -> subst
  | `Mu _ -> assert false
  | `Int -> `Int
  | `Ref (false, t) -> `Ref (false, unfold_fltype subst t)
  | `Ref (true, _) -> failwith "Already unfolded ref under a mu binder?!?!?"
  | `Tuple tl -> `Tuple (List.map (unfold_fltype subst) tl)
  | `IntArray -> `IntArray
  | (`Lock _ | `ThreadID _) as t -> t

(** walks the type, unfolding all mu binders once *)
let rec deep_type_normalization : fltype -> fltype = function
  | `Mu (`Ref (false, t)) -> `Ref (true, unfold_fltype (`Mu (`Ref (false, t))) t)
  | `Mu (`Ref (true, _)) -> failwith "broken invariant"
  | `Mu _ -> assert false
  | `Int -> `Int
  | `Tuple tl -> `Tuple (List.map deep_type_normalization tl)
  | `Ref (b, t) -> `Ref (b, deep_type_normalization t)
  | `IntArray -> `IntArray
  | `TVar -> assert false
  | (`Lock _ | `ThreadID _) as t -> t

let rec simple_to_fltype ?tvar : r_typ -> fltype = function
  | `Mu (id, t) ->
      assert (tvar = None);
      `Mu (simple_to_fltype ~tvar:id t)
  | `Int -> `Int
  | `Array `Int -> `IntArray
  | `Ref t -> `Ref (false, simple_to_fltype ?tvar t)
  | `TVar id ->
      assert (Option.map (( = ) id) tvar |> Option.value ~default:false);
      `TVar
  | `Tuple tl -> `Tuple (List.map (simple_to_fltype ?tvar) tl)
  | `Lock pte -> `Lock (SM.map simple_to_fltype pte)
  | `ThreadID pte -> `ThreadID (SM.map simple_to_fltype pte)

let%lq get_function_type f_name ctxt =
  let { f_type; _ } = StringMap.find f_name ctxt.fenv in
  f_type

let%lq get_in_relation f_name ctxt =
  let { in_rel = ir; _ } = StringMap.find f_name ctxt.fenv in
  ir

let%lq get_out_relation f_name ctxt =
  let { out_rel = o_rel; _ } = StringMap.find f_name ctxt.fenv in
  o_rel

let%lq get_function_info f_name ctxt = StringMap.find f_name ctxt.fenv
let%lq copy_state ctxt = ctxt

(** Get the name of the given relation *)
let get_relation_ident ((n, _, _) : relation) = n

(** [omit_map[rel] |= set]; Add omit set *)
let merge_havoc_omit rel set omit_map =
  StringMap.update rel
    (function None -> Some set | Some x -> Some (P.PathSet.union x set))
    omit_map

let%lm set_havoc_state ~rel havoc_state ctxt =
  {
    ctxt with
    havoc_set = havoc_state;
    omit_set = merge_havoc_omit rel havoc_state ctxt.omit_set;
  }

let%lm add_havoc_state ~rel havoc_state ctxt =
  {
    ctxt with
    havoc_set = P.PathSet.union ctxt.havoc_set havoc_state;
    omit_set = merge_havoc_omit rel havoc_state ctxt.omit_set;
  }

let%lq get_havoc_state ctxt = ctxt.havoc_set

(** [get_bound_type e_id ctxt]: Get the type of the expression at [e_id] *)
let%lq get_bound_type e_id ctxt = IntMap.find e_id ctxt.let_types

(** Get the name of the current function being inferred *)
let%lq get_curr_fun ctxt = Option.value ~default:"main-fn" ctxt.curr_fun

(** [get_pte_relation ?fn v ctxt ]: Get the PTE relation held by [v] in function [fn] *)
let%lq get_pte_relation ?fn v ctxt =
  let _, curr_fun = get_curr_fun ctxt in
  let fn = Option.value ~default:curr_fun fn in
  try SPM.find (fn, v) ctxt.pte_rel
  with _ ->
    failwith
    @@ Printf.sprintf
         "In function %s, %s is neither a lock type nor a thread ID type" fn v

let mk_relation lhs op rhs = RT.{ rel_op1 = lhs; rel_cond = op; rel_op2 = rhs }

(** [ty] tracks the type of the arguments (used for "type inference" when dumping SMT clauses) *)
let rel ~ty k = Relation (k, ty)

(* TODO: make this function actually useful... *)
let path_type p = if P.is_nullity p then ZBool else ZInt

(** Add [z3_types] to each path in the given list of paths *)
let type_paths : P.path list -> (P.path * z3_types) list =
  List.map (fun p -> (p, path_type p))

(** Add the constraint [curr_relation => op1 cond op2] *)
let%lm add_assert op1 cond op2 curr_relation ctxt =
  let ante = [ PRelation (curr_relation, [], None) ] in
  let relation = rel ~ty:ZInt @@ mk_relation op1 cond op2 in
  { ctxt with impl = (ante, relation) :: ctxt.impl }

let add_assert_cond assert_cond curr_relation =
  let lift_to_imm = function IVar v -> Ap (P.var v) | IInt i -> IConst i in
  add_assert
    (lift_to_imm assert_cond.rop1)
    assert_cond.cond
    (lift_to_imm assert_cond.rop2)
    curr_relation

(** One of the two "oracles" used to translate from ownership operations on reference types
   to access paths pointing to concrete integers. Flow inference does not track ownership explicitly,
   simply the paths TO INTEGER VALUES that are havoced. By contrast, the ownership inference only tracks
   the ownership results at each ownership operation; these results give the ownership of a reference,
   which has no representation in the abstract state.

   The translation works as follows. For a value path at some generation operation, we walk the path upwards
   until we reach the first path to a reference constructor. We then look that path up in the ownership_ops map
   produced by the ownership inference.

   This process is, unfortunately, _extremely_ brittle; it's quite easy to pass in a path that is not
   rooted in the desired path. Of _particular_ importance is the distinction between the havoc state of the path
   to reference r, and the havoc state of paths "beneath" r. In the former case, the havoc state of r (and indeed, r's null flag)
   is determined by the containing path of r. Thus, the null flag of a local variable [v] is *never* havoced, even if
   the ownership of the reference stored at [v] drops to 0; that ownership describes the havoc status of all paths
   _below_ [v], whereas there is no containing reference for [v] itself. It is unfortunate that the path denoting the
   null flag of [v] happens to be represented as an extension (and thus "beneath") [v]; this requires an annoying special
   case when doing havoc queries, but *believe me*, it's far more annoying to use another strategy.
 *)
let rec havoc_oracle ctxt ml p =
  Log.debug ~src:"FLOW-OWN" !"Looking for %{P} @ %{sexp:OI.magic_loc}" p ml;
  let from_path p_ =
    let o = OI.GenMap.find (ml, p_) ctxt.o_hints.OI.gen in
    o = 0.0
  in
  match P.tail p with
  | Some `Deref | Some `Ind | Some `Elem -> from_path @@ P.parent p
  | Some _ -> havoc_oracle ctxt ml @@ P.parent p
  | None -> false

let%lq split_oracle sl ctxt =
  let from_path p =
    Log.debug ~src:"FLOW-OWN" !"Splitting %{P} @ %{sexp:OI.split_loc}" p sl;
    let f1, f2 = OI.SplitMap.find (sl, p) ctxt.o_hints.OI.splits in
    let to_flag b = if b then `Havoc else `Stable in
    (to_flag (f1 = 0.0), to_flag (f2 = 0.0))
  in
  let rec loop p1 p2 =
    match (P.tail p1, P.tail p2) with
    | None, _ -> (`Trivial, `Trivial)
    | _, None -> (`Trivial, `Trivial)
    | Some a, Some b ->
        let () = assert (a = b) in
        if a = `Deref || a = `Ind || a = `Elem then from_path @@ P.parent p1
        else loop (P.parent p1) (P.parent p2)
  in
  loop

let%lq gen_for_alias e_id ctxt = havoc_oracle ctxt (OI.MAlias e_id)
let%lq gen_oracle ml ctxt = havoc_oracle ctxt ml

let rec lift_refinement ?(map = Fun.id) ?nu_arg : RT.refinement -> clause list =
  let lift_symbolic_ap = map in
  let lift_symbolic_imm : RT.rel_imm -> concr_arg = function
    | RT.RConst i -> IConst i
    | RT.RAp p -> Ap (lift_symbolic_ap p)
  in
  RT.(
    function
    | Top -> []
    | And (r1, r2) ->
        lift_refinement ~map ?nu_arg r1 @ lift_refinement ~map ?nu_arg r2
    | ConstEq i ->
        [ rel ~ty:ZInt @@ mk_relation (Ap (Option.get nu_arg)) "=" (IConst i) ]
    | Relation ({ rel_op1 = Nu; _ } as r) ->
        [
          rel ~ty:ZInt
            {
              r with
              rel_op1 = Ap (Option.get nu_arg);
              (* Replace [Nu] with the concrete access path [nu_arg] *)
              rel_op2 = lift_symbolic_imm r.rel_op2;
            };
        ]
    | Relation ({ rel_op1 = RImm i; _ } as r) ->
        [
          rel ~ty:ZInt
            {
              r with
              rel_op1 = lift_symbolic_imm i;
              rel_op2 = lift_symbolic_imm r.rel_op2;
            };
        ]
    | NamedPred (nm, sym_names) ->
        let nu_arg = Option.get nu_arg in
        let named_args = List.map lift_symbolic_ap sym_names in
        let val_args = List.map (fun l -> Ap l) @@ (nu_arg :: named_args) in
        [ NamedRel (nm, val_args) ])

(** Extract the type referred to by the [path] in [tyenv] *)
let path_simple_type tyenv path =
  let rec loop (path : P.path) k =
    match P.tail path with
    | None -> (
        match (path : P.path :> P.root * 'a * 'b) with
        | P.Var v, _, _ ->
            k @@ List.assoc v tyenv
            (* Get the type of the root [v], follow the given path [path] by continuation [k], and get its type *)
        | _ -> failwith "not supported")
    | Some `Deref ->
        loop (P.parent path) (function
          | `Ref (_, t) -> k t
          | t ->
              failwith
              @@ Printf.sprintf "Unexpected simple type %s for path %s"
                   (fltype_to_string t) (P.to_z3_ident path))
    | Some (`Proj i) ->
        loop (P.parent path) (function
          | `Tuple tl -> k @@ List.nth tl i
          | _ -> assert false)
    | _ -> failwith "Not supported"
  in
  loop path (fun i -> i)

let is_null_flag = true
let is_nonnull_flag = false

let%lm add_null_path_check curr_rel null_flag_path ctxt =
  if not ctxt.null_checks then ctxt
  else
    {
      ctxt with
      impl =
        ( [ PRelation (curr_rel, [], None) ],
          rel ~ty:ZBool
          @@ mk_relation (Ap null_flag_path) "=" (BConst is_nonnull_flag) )
        :: ctxt.impl;
    }

(** [add_null_check curr_rel pointer_path]
    - [curr_rel]: Current relation
    - [pointer_path]: Path of reference guaranteed not to be null *)
let add_null_check curr_rel pointer_path =
  add_null_path_check curr_rel @@ P.to_null pointer_path

(** Generate nullity well-formedness conditions for the relation
   arguments, using the argument subst. Iterates the arguments looking for null-flags,
   finds the null flag of the enclosing reference (if any) and then generates a well-formedness
   condition.
*)
let null_pre (_, args, _) subst =
  let subst_ap p =
    if List.mem_assoc p subst then List.assoc p subst else Ap p
  in
  let rec parent_null_loop p =
    match P.tail p with
    | None -> None
    | Some `Deref -> Some (P.to_null @@ P.parent p)
    | Some _ -> parent_null_loop @@ P.parent p
  in
  List.filter_map
    (fun (p, _) ->
      if not @@ P.is_nullity p then None
      else
        P.parent p |> parent_null_loop
        |> Option.map (fun parent -> NullCons (subst_ap parent, subst_ap p)))
    args

(** To havoc an access path, we simply generate a fresh name,
   universally quantify over it, and leave it completely unconstrained.
   This is accomplished by simply generating a fresh name not generated by
   "regular" program analysis.
*)
let to_havoc d = Printf.sprintf "havoc!%d!%s" d

let havoc_ap d p =
  P.map_root (to_havoc d)
  @@ if P.is_template p then P.root_at ~child:p ~parent:(P.var "$tmp") else p

(** "Passthrough access paths" or (pass ap) are used for "weak" copies
   of summary values. Generally when copying a value from x to y,
   it is sufficient to substitution x for y in the output relation. However,
   this implies that x and y *must* be equal; if x and y are summary locations this leads
   to all sorts of problems. Suppose x is refined in current relation R, and
   we want to (weakly)  x to the freshly created variable y. Then, it suffices to
   to the following: R(x) /\ R(y) => Q(x, y). x and y are not necessarily equal, but both
   satisfy the same properties. However, suppose y is already in scope at the time of the copy,
   then we will have:

   R(x, y) /\ R(y, y) => Q(x, y)

   Which causes all sorts of problems (in particular, it implies that only values
   that satisfy the current and new refinements are acceptable.
   Thus we have the *passthrough* access paths which are used as dummy values here.
   So, in the example above, we would have:

   R(x, y!pass) /\ R(y, y!pass) => Q(x, y)

   Pass aps are also used as a kind of priming mechanism, to generate a version of the access
   path that won't be used for anything else. They are used in aliasing and recursive
   refinements.
*)

let to_pass_ap = P.map_root (fun s -> "pass!" ^ s)
let lift_copy (s, d) = (s, Ap d)

(** Add the constraint [ante => conseq] *)
let%lm add_implication ante conseq ctxt =
  { ctxt with impl = (ante, conseq) :: ctxt.impl }

(** The flow datatype represents high level flows which
   are then compiled down to the necessary substitutions on the output
   relation.
*)
let flow_to_subst (i : int) : flow -> P.path * concr_arg = function
  | Havoc p -> (p, Ap (havoc_ap i p))
  | Const (p, c) -> (p, IConst c)
  | Copy (p1, p2) -> (p2, Ap p1)
  | NullConst (p, b) -> (p, BConst b)

(** Generate the constraint [in_rel => out_rel].
    Substitute the arguments of [out_rel] using [subst]. *)
let%lm add_relation_flow ?out_ctxt ?(pre = []) (subst : flow list)
    (in_rel : relation) (out_rel : relation) ctxt =
  let lifted_subst : (P.path * concr_arg) list =
    List.mapi flow_to_subst subst
  in
  let ante = PRelation (in_rel, [], None) :: pre in
  let conseq = PRelation (out_rel, lifted_subst, out_ctxt) in
  { ctxt with impl = (ante, conseq) :: ctxt.impl }

(** For a given type, generate all paths to "address" values
   of that type. In other words, given a root variable of type t,
   what are the access paths of the values reachable from that root variable.
*)
let type_to_paths ?(pre = false) root (ty : fltype) =
  let add_path pre under_ref under_mu acc p =
    let paths =
      (if under_ref && (not under_mu) && pre then [ P.pre p ] else []) @ [ p ]
    in
    paths @ acc
  in
  let rec loop under_ref under_mu acc p : fltype -> P.path list = function
    | `Int -> add_path pre under_ref under_mu acc p
    | `Ref (_, t) ->
        (* Add the null flag of the reference which the path [p] points to, to [acc] *)
        let acc = add_path pre under_ref under_mu acc (P.to_null p) in
        loop true under_mu acc (P.deref p) t
    | `Tuple tl ->
        fold_lefti
          (fun i acc t -> loop under_ref under_mu acc (P.t_ind p i) t)
          acc tl
    | `IntArray ->
        List.fold_left
          (add_path false under_ref under_mu)
          acc
          [ P.len p; P.ind p; P.elem p ]
    | `Mu t -> loop under_ref true acc p t
    | `TVar -> acc
    | `Lock _ | `ThreadID _ ->
        (* No integer or null flag reachable from lock or thread id *)
        acc
  in
  loop false false [] root ty

(** state stepper for extending a path via type walking; see below *)
let path_step k p =
  match k with
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

(**
   Walk a type, using a callback mechanism to control the walk.

   This takes two functions, a stepper, and an processor. The processor is called
   for the terminal locations in a type, namely:
   + the length of an array
   + the contents of an array
   + the index of an arry
   + the nullity of a reference
   + any integer types

   At these terminal locations, the processor function [f] is called with the current state
   (see below) and the accumulator. This accumulator is returned as the result of the walk.

   During the walk, during each step this function calls the [step] function to either update the state or short circuit the walk.
   The initial state of the walk is given by the [st] argument. The behavior of the walk is described to the [step] function
   by passing in the current state as the second argument, and a variant type with the following values, describing the the traversal.

   The step function may return a variant with three possible tags:
   + `K, which has a function that expects the current type, the accumulator; the return value is immediately returned as the result of the walk (no further walking)
   + `Cont st -> continue the walk with the new state [st]
   + `ContWith (f,st) -> a combination of the above. The first element is a function as described in `K; the second element is as described in `Cont. The
   function is first applied to give the new accumulator, and the walk continues with the new accumulator and new state.
*)
let rec walk_type ty step f st acc =
  let continue ~acc mst k =
    match mst with
    | `K f_ -> f_ ty acc
    | `ContWith (f, st) ->
        let acc = f ty acc in
        k st acc
    | `Cont st -> k st acc
  in
  match ty with
  | `Int -> f st acc
  | `Ref (false, t) ->
      let mst = step `Null st in
      continue ~acc mst (fun st' acc ->
          let acc = f st' acc in
          let mst = step `Ref st in
          continue ~acc mst (walk_type t step f))
  | `Ref (true, t) ->
      let mst = step `Null st in
      continue ~acc mst (fun st' acc ->
          let acc = f st' acc in
          let mst = step `Summ st in
          continue ~acc mst (fun st' acc ->
              let mst = step `Ref st' in
              continue ~acc mst (walk_type t step f)))
  | `Tuple tl ->
      fold_lefti
        (fun i acc t ->
          let mst = step (`Tuple i) st in
          continue ~acc mst (walk_type t step f))
        acc tl
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
                  continue ~acc mst f)))
  | `Lock _ | `ThreadID _ -> failwith "not implemented in flowinference"

(** Walk two paths in parallel according to the type ty. Unlike type_walk, this
   walk function only calls the step function when:
   + entering an unfolded ref (see [get_recursive_roots])
   + stepping under a ref
   + stepping under a mu
   + stepping into array memory

   In addition, this walker extends the state to automatically track the paths from in_ap and out_ap
   during the walk of the type. The step function return type is the same as in [walk_type], however
   it may additionally return [`ContPath (in_ap,out_ap, st)] which continues the walk in a new state [st],
   but overriding the two current paths with in_ap and out_ap respectively.
*)
let parallel_type_walk in_ap out_ap ty step f st acc =
  walk_type ty
    (fun k (in_ap, out_ap, st) ->
      let user_step constr kind =
        let mst = step kind (in_ap, out_ap) st in
        match mst with
        | `K f -> `K f
        | `ContWith (f, st) -> `ContWith (f, (constr in_ap, constr out_ap, st))
        | `Cont st -> `Cont (constr in_ap, constr out_ap, st)
        | `ContPath (in_ap, out_ap, st) -> `Cont (in_ap, out_ap, st)
      in
      let parallel_step constr = `Cont (constr in_ap, constr out_ap, st) in
      match k with
      | `Ref -> user_step P.deref `Ref
      | `Mu -> user_step Fun.id `Mu
      | `Array -> user_step Fun.id `Array
      | `Ind -> parallel_step P.ind
      | `Elem -> parallel_step P.elem
      | `Length -> parallel_step P.len
      | `Tuple i -> parallel_step ((Fun.flip P.t_ind) i)
      | `Null -> parallel_step P.to_null
      | `Summ -> user_step Fun.id `Summ)
    (fun (in_ap, out_ap, st) acc -> f st in_ap out_ap acc)
    (in_ap, out_ap, st) acc

(** A module for tracking the recursive relations attached to mu binders.
   These recursive relations describe the relationship between values underneath
   a mu binder and the values yielded by a one-level unfolding of that mu type.

   These are tracked separately from the monolithic program state relations
*)
module RecRelations = struct
  (** Mu chain is designed to track the access paths to elements under a mu
     binder. In particular, a mu chain splits an access path into two components,
     the path to the mu binder, and then the path to the value in question with respect
     to the mu binder.

     MuChains may be converted easily to regular access paths with the to_concr method.
     The most convenient way to construct one is to use the raw_stepper as the state stepper
     for the [walk_type] function.
  *)
  module MuChain = struct
    type t = P.concr_ap * P.concr_ap option [@@ocaml.warning "-34"]

    let to_concr (s, p) =
      Option.fold ~none:s ~some:(fun parent -> P.root_at ~child:s ~parent) p

    let step_mu (s, p) =
      assert (p = None);
      (P.template, Some s)

    let get_mu_path (s, p) = Option.map (fun p -> (s, p)) p

    let raw_stepper k (s, p) =
      match k with
      | `Mu -> `Cont (step_mu (s, p))
      | _ -> `Cont (path_step k s, p)
  end

  (** Get the paths to all recursive roots. The _root_ of a recursive
     type is the ref type constructor yielded by a one-level unfolding of a recursive type.
     These ref constructors have the second element set to true, and this causes the `Summ step to be
     emitted by the type walker. The paths to these ref types are collected, along with the types *)
  let get_recursive_roots root ty =
    walk_type ty
      (fun k s ->
        match k with
        | `Summ -> `K (fun ty acc -> (s, ty) :: acc)
        | _ -> `Cont (path_step k s))
      (fun _ acc -> acc)
      root []

  (** Get the paths to all mu binders in the type that is rooted in path [root] *)
  let get_mu_binders root ty =
    walk_type ty
      (fun k s ->
        match k with
        | `Mu -> `K (fun _ acc -> s :: acc)
        | _ -> `Cont (path_step k s))
      (fun _ acc -> acc)
      root []

  let mu_transposition_of ~ty path =
    get_mu_binders P.template ty
    |> List.map (fun binders -> P.root_at ~child:path ~parent:binders)

  let update_rel_map dst rel = P.PathMap.add dst rel

  let set_recursive_rel dst rel ctxt =
    { ctxt with recursive_rel = update_rel_map dst rel ctxt.recursive_rel }

  (** Because a mu relation may be freely duplicated between mu binders on copies, we
     do not generate the paths with respect to a concrete root, but rather a template.
  *)
  let recursive_rel_for ~e_id ty dst ctxt =
    let name = Printf.sprintf !"%{P}-%d-%s" dst e_id "mu" in
    let args =
      type_to_paths P.template ty |> List.map (fun p -> (p, path_type p))
    in
    let rel = (name, args, ExprMu (e_id, dst, `Flow)) in
    let ctxt =
      set_recursive_rel dst rel
      @@ { ctxt with relations = rel :: ctxt.relations }
    in
    (ctxt, rel)

  (** Assuming a path [p] is given from a mu binder to some value, the mu transposition
     for [p] gives all paths which point to the same relative position underneath all
     mu-binders that appear after a one level unfolding of the enclosing mu binder. In other words,
     after unfolding a recursive type, the mu transposition of [p] gives the same relative position
     in all new instances of the mu binder in the unfolded type.
  *)
  let recursive_havoc_subst ty havoc_paths =
    havoc_paths
    |> ListMonad.bind (fun p -> p :: mu_transposition_of ~ty p)
    |> List.mapi (fun i s -> (s, Ap (havoc_ap i s)))

  (** Add an implication with clauses given by [ante] to the mu relation given by [dst_rel].
     The dst_root is the concrete path of to the mu binder described by [dst_rel], it is
     used to look up havoc information in the [by_havoc] map. This havoc information indicates
     which elements in the unfolding must be havoced; this is computed by the recursive_havoc_subst.
  *)
  let impl_with_havoc ?out_shift ~by_havoc ~ante dst_root dst_rel ctxt =
    let havoc_subst =
      P.PathMap.find_opt dst_root by_havoc
      |> Option.map (fun (ty, havoc_paths) ->
             recursive_havoc_subst ty @@ P.PathSet.elements havoc_paths)
      |> Option.value ~default:[]
    in
    let omit_paths =
      List.fold_left
        (fun acc (p, _) -> P.PathSet.add p acc)
        P.PathSet.empty havoc_subst
    in
    {
      ctxt with
      impl = (ante, PRelation (dst_rel, havoc_subst, out_shift)) :: ctxt.impl;
      omit_set =
        merge_havoc_omit (get_relation_ident dst_rel) omit_paths ctxt.omit_set;
    }

  (** Generate a fresh recursive relation for the mu binder at dst_root, and then generate an implication
     from [ante] *)
  let recursive_rel_with_havoc ~by_havoc ~e_id ~ante dst_root ty (ctxt : ctxt) =
    let ctxt, rel = recursive_rel_for ~e_id ty dst_root ctxt in
    impl_with_havoc ~by_havoc ~ante dst_root rel ctxt

  let%lm null_for_var ~e_id ~ty var ctxt =
    get_recursive_roots (P.var var) ty
    |> List.fold_left
         (fun ctxt (root, ty) ->
           let args =
             type_to_paths P.template ty |> List.map (fun p -> (p, path_type p))
           in
           get_mu_binders root ty
           |> List.fold_left
                (fun ctxt bind ->
                  let name = Printf.sprintf !"null-%d-%{P}-%s" e_id bind "mu" in
                  let rel = (name, args, ExprMu (e_id, bind, `Null)) in
                  let grounding_subst =
                    List.filter_map
                      (fun (s, p) ->
                        match p with
                        | ZBool ->
                            let () = assert (P.is_nullity s) in
                            Some (s, BConst is_null_flag)
                        | _ -> None)
                      args
                  in
                  set_recursive_rel bind rel
                    {
                      ctxt with
                      relations = rel :: ctxt.relations;
                      impl =
                        ([], PRelation (rel, grounding_subst, None))
                        :: ctxt.impl;
                    })
                ctxt)
         ctxt
end

type copy_spec = {
  direct_copies : (P.concr_ap * P.concr_ap) list;
      (** copy concrete value v at path p1 to path at p2 *)
  weak_copies : (P.concr_ap * P.concr_ap * fltype) list;
      (** Copy a recursive type of type [t] rooted at [p1] to [p2]
                                                          NB that the [root] of a recursive type is the reference yielded by the
                                                          unfolding of a recursive type (all mu binders appear underneath
                                                          a reference type *)
}
(** A copy specification describes how to copy values from one location to another *)

let empty_copy = { direct_copies = []; weak_copies = [] }

let add_weak src dst ty cs =
  { cs with weak_copies = (src, dst, ty) :: cs.weak_copies }

let add_direct src dst cs =
  { cs with direct_copies = (src, dst) :: cs.direct_copies }

let ccat a1 a2 =
  {
    direct_copies = a1.direct_copies @ a2.direct_copies;
    weak_copies = a1.weak_copies @ a2.weak_copies;
  }

(** Return the flow from [in_ap] to [out_ap] as [copy_spec].
    Note: [in_ap] and [out_ap] are not necessarily a path to a single integer value, 
          but they may be the one to a tuple or to something more complicated.
          Therefore, [parallel_type_walk] is needed to follow all the paths reachable from [in_ap] and [out_ap]. *)
let compute_copies in_ap out_ap ty : copy_spec =
  parallel_type_walk in_ap out_ap ty
    (fun k (in_ap, out_ap) () ->
      match k with
      | `Summ -> `K (fun ty -> add_weak in_ap out_ap ty)
      | _ -> `Cont ())
    (fun () -> add_direct)
    () empty_copy

(** Transforms a copy spec into a stream of atomic transfer specifications
   Each atomic transfer specification indicates that a value described at path p
   should be copied (strongly or weakly) to path q. The third component is either `Direct,
   in which case the copy is "strong", of `Mu in which case the copy should be weak. The mu tag
   has three elements: the path from the mu binder to the element being copied, the
   source path to the enclosing mu binder, the destination path to the enclosing mu binder,
   and the [ty] at the root of the recursive type instance (i.e., the type given after unfolding
   the mu).
*)
let to_copy_stream { direct_copies; weak_copies } =
  let l = List.map (fun (s, d) -> (s, d, `Direct)) direct_copies in
  List.fold_left
    (fun acc (s, d, ty) ->
      parallel_type_walk s d ty
        (fun k (in_ap, dst_ap) stack ->
          match k with
          | `Mu -> `ContPath (P.template, dst_ap, Some (in_ap, dst_ap))
          | `Summ | `Ref | `Array -> `Cont stack)
        (fun stack in_ap out_ap acc ->
          let s = (in_ap, Option.map fst stack) in
          let concr_in = RecRelations.MuChain.to_concr s in
          let acc' = (concr_in, out_ap, `Direct) :: acc in
          Option.fold ~none:acc'
            ~some:(fun (in_mu, out_mu) ->
              (concr_in, out_ap, `Mu (in_ap, in_mu, out_mu, ty)) :: acc)
            stack)
        None acc)
    l weak_copies

(** Compute the positions of the mu binders transfered from source to destination as described
   by [weak_copies]. This stream is later used to copy/transfer recursive relation information *)
let to_mu_copies { weak_copies; _ } =
  ListMonad.bind
    (fun (s, d, ty) ->
      RecRelations.get_mu_binders P.template ty
      |> List.map (fun st ->
             ( st,
               P.root_at ~child:st ~parent:s,
               P.root_at ~child:st ~parent:d,
               ty )))
    weak_copies

(** For {[let patt = path in ... ]}, return the flow from [path] to [patt] as [copy_spec]. *)
let compute_patt_copies path patt ty : copy_spec =
  let rec loop patt path ty acc =
    match (patt, ty) with
    | PNone, _ -> acc
    | PVar v, `Int -> add_direct path (P.var v) acc
    | PVar v, ty -> ccat (compute_copies path (P.var v) ty) acc
    | PTuple t, `Tuple tl ->
        fold_left2i (fun i acc p t -> loop p (P.t_ind path i) t acc) acc t tl
    | PTuple _, _ -> assert false
  in
  loop patt path ty empty_copy

module Havoc = struct
  type mu_havoc = (fltype * P.PathSet.t) P.PathMap.t
  (** This mu_havoc type is the type used for the by_havoc map described above *)

  type havoc_state = {
    havoc : P.PathSet.t;  (** These paths are havoced *)
    stable : P.PathSet.t;  (** These paths are stable *)
    mu_havoc : mu_havoc;
        (** The havocing under a mu binder is as described above *)
  }
  (** A type to track which paths are stable (i.e., not havoced) and those that are havoced by an ownership operation. *)

  let empty_havoc_state =
    {
      havoc = P.PathSet.empty;
      stable = P.PathSet.empty;
      mu_havoc = P.PathMap.empty;
    }

  (** if flag [f] is true, then flag [p] as havoc, otherwise, treat it at stable *)
  let add_havoc p f m =
    if f then { m with havoc = P.PathSet.add p m.havoc }
    else { m with stable = P.PathSet.add p m.stable }

  (** If [f] is havoced, then for the [binder] whose unfolded type is [ty], treat the mu path
     as havoced *)
  let add_mu_havoc ~binder ~ty p f m =
    if f then
      {
        m with
        mu_havoc =
          P.PathMap.update binder
            (function
              | None -> Some (ty, P.PathSet.singleton p)
              | Some (ty', set) ->
                  let () = assert (ty = ty') in
                  Some (ty, P.PathSet.add p set))
            m.mu_havoc;
      }
    else m

  let to_rec_havoc { mu_havoc; _ } = mu_havoc

  (** Compute the havoc state for a reference type ascribed to null *)
  let%lm update_null_havoc ~e_id ~ty var ctxt =
    let ref_havoc p =
      OI.GenMap.find (OI.MGen e_id, p) ctxt.o_hints.OI.gen = 0.0
    in
    let hstate =
      walk_type ty
        (fun k (f, p) ->
          let f = match k with `Ref | `Array -> ref_havoc p | _ -> f in
          `Cont (f, path_step k p))
        (fun (f, p) acc -> add_havoc p f acc)
        (false, P.var var)
        empty_havoc_state
    in
    {
      ctxt with
      havoc_set =
        P.PathSet.union hstate.havoc
        @@ P.PathSet.diff ctxt.havoc_set hstate.stable;
    }
end

module H = Havoc

(** For a set of flows (represented by an output substitution), augment it with a rehavocing of all havoced
   locations
*)
let augment_havocs flows havoc_set =
  List.filter (fun (p, _) -> not (P.PathSet.mem p havoc_set)) flows
  |> P.PathSet.fold (fun p acc -> (p, Ap (havoc_ap 0 p)) :: acc) havoc_set

(* Generate flows from a set of paths to be havoced *)
let havoc_set_to_subst : P.PathSet.t -> (P.path * concr_arg) list =
  augment_havocs []

(**
   Compute the the substitutions necessary for the copy spec as described below.

   This function returns a 4-ary tuple: (hstate, rename_copy, copy_flows, out_flows).
   + hstate: the new havoc state (used in apply copies and elsewhere) describing the
   havoc state after references are tranferred via the [copies]. The [sl] argument gives the ownership location
   for the split operations.
   + rename_copy and copy_flows: Used to implement the pass, weak copies described above. copy_flows renames the
   the SOURCE location to the destination location; this is applied to the arguments of the input relation. Without
   further renaming in the output, the result of this renaming becomes the new value of the location in the destination relation.
   rename_copy renames the destination locations to dummy _pass_ copies.
   + out_flows: these are substitutions describing the direct flow of values from inputs to outputs; to effect a copy of
   a to b, we renamed b to a in the output, thereby ensuring it has the value of a as described by the input relation.
*)
let compute_flows ~sl copies ctxt =
  let _, split_oracle = split_oracle sl ctxt in
  to_copy_stream copies
  |> List.fold_left
       (fun (hstate, rename_copy, copy_subst, out_subst) (src, dst, k) ->
         let h_in, h_out = split_oracle src dst in
         let add_havoc p f ostate =
           (* Trivial ownership transfers do not affect havoc status. These happen when a havoed value flows out from
              under a reference constructor (although to be precise, we shouldn't say that a value is havoced, but a memory location
              is). In that case, the havoc state of the input and output should be unchanged. *)
           if f = `Trivial then ostate
           else Havoc.add_havoc p (f = `Havoc) ostate
         in
         let hstate = add_havoc src h_in @@ add_havoc dst h_out hstate in
         match k with
         | `Direct ->
             (hstate, rename_copy, copy_subst, (dst, Ap src) :: out_subst)
         | `Mu (under_mu_path, s, d, ty) ->
             let () =
               assert (h_in <> `Trivial);
               assert (h_out <> `Trivial)
             in
             let hstate =
               (* recall that under_mu_path is the path relative to a mu binder, s and d are both the paths to the mu_binder, and ty is the unfolded type
                  of the mu binder
               *)
               Havoc.add_mu_havoc ~binder:s ~ty under_mu_path (h_in = `Havoc)
                 hstate
               |> Havoc.add_mu_havoc ~binder:d ~ty under_mu_path (h_out = `Havoc)
             in
             ( hstate,
               (dst, Ap (to_pass_ap src)) :: rename_copy,
               (src, Ap dst) :: copy_subst,
               out_subst ))
       (Havoc.empty_havoc_state, [], [], [])

(** Copy the recursive relation for a mu binder at p to a mu binder at q. If there
   is any havocing, we must generate a fresh relation and perform implications, otherwise
   it suffices to symbolically copy the name *)
let copy_rel ~by_havoc ~e_id ~ty src_rel dst_root ctxt =
  if P.PathMap.mem dst_root by_havoc then
    RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id
      ~ante:[ PRelation (src_rel, [], None) ]
      dst_root ty ctxt
  else RecRelations.set_recursive_rel dst_root src_rel ctxt

(** Apply the copies from [copies], including any high level flows from [flows].

   The [havoc] flag determines whether all havoced locations should be re-havoced or only those freshly made 0.
   This flag is set to true for calls and assignments to indicate uncertainty about which locations are havoced.

   [pre] is an optional list of clauses to add to the generated implication. The [in_rel] and [out_rel]
   are the source and target relations.
 *)
let%lm apply_copies ?out_rec_rel ~havoc:havoc_flag ~sl ?(flows = []) ?pre copies
    in_rel out_rel ctxt =
  let hstate, rename_copy, copy_flows, out_flows =
    compute_flows ~sl copies ctxt
  in
  (* The mu binders that are copied *)
  let mu_copies = to_mu_copies copies in
  let havoc_set = ctxt.havoc_set in
  (* update the havoc set according to the new havoc info computed by compute copies

     [havoc_set := havoc + (havoc_set - stable)]
     - havoc_set: a set of currently havoced paths
     - havoc: a set of newly havoced paths
     - stable: a set of newly non-havoced paths *)
  let havoc_set =
    P.PathSet.union hstate.H.havoc @@ P.PathSet.diff havoc_set hstate.H.stable
  in
  (* which paths should be havoc?

     If [havoc_flag] then havoc all the paths to be havoced
     Else havoc only paths which turned out to be havoced just now *)
  let applied_havocs = if havoc_flag then havoc_set else hstate.H.havoc in
  let flows = List.mapi flow_to_subst flows in
  (* the output substitution; augments direct copies with those produced by the high level flows optional argument
     and the havoc information *)
  let out_flows = augment_havocs (flows @ out_flows) applied_havocs in
  let pre =
    Option.value ~default:[] pre
    @
    (* if there are any weak copies, then we must use the duplication trick described with pass ap *)
    if List.compare_length_with copy_flows 0 > 0 then
      [
        PRelation (in_rel, rename_copy, None);
        PRelation (in_rel, rename_copy @ copy_flows, None);
      ]
    else [ PRelation (in_rel, [], None) ]
  in
  let conseq = PRelation (out_rel, out_flows, None) in
  let ctxt =
    let by_havoc = H.to_rec_havoc hstate in
    (* the src and dst elements here is the path to a mu binder in the source and destination respectively *)
    List.fold_left
      (fun ctxt (_, src, dst, ty) ->
        let () = assert (P.PathMap.mem src ctxt.recursive_rel) in
        let e_id =
          match sl with OI.SRet e_id | OI.SBind e_id | OI.SCall e_id -> e_id
        in
        let src_rel = P.PathMap.find src ctxt.recursive_rel in
        (* why on earth are we copying the source relation to itself? Because if the source
           ownership is dropped to 0, we have to havoc *)
        let ctxt = copy_rel ~by_havoc ~e_id ~ty src_rel src ctxt in
        match out_rec_rel with
        | Some (direct_flow, _) ->
            (* if the destination is a return value recursive relation, use that as the target of implication *)
            P.PathMap.find_opt dst direct_flow
            |> Option.fold ~none:ctxt ~some:(fun rel ->
                   RecRelations.impl_with_havoc ~by_havoc
                     ~ante:[ PRelation (src_rel, [], None) ]
                     dst rel ctxt)
        | None -> copy_rel ~by_havoc ~e_id ~ty src_rel dst ctxt)
      ctxt mu_copies
  in
  let ctxt =
    match out_rec_rel with
    | None -> ctxt
    | Some (_, extra_rec_flows) ->
        (* copy the recursive relation from input arguments to output flows *)
        List.fold_left
          (fun ctxt (src, rel) ->
            let in_rel = P.PathMap.find src ctxt.recursive_rel in
            {
              ctxt with
              impl =
                ([ PRelation (in_rel, [], None) ], PRelation (rel, [], None))
                :: ctxt.impl;
            })
          ctxt extra_rec_flows
  in
  {
    ctxt with
    havoc_set;
    impl = (pre, conseq) :: ctxt.impl;
    omit_set =
      merge_havoc_omit (get_relation_ident out_rel) havoc_set ctxt.omit_set;
  }

module IdMap (M : Map.S) : sig
  type t

  val id_map : t
  val find : M.key -> t -> M.key
  val add : M.key -> M.key -> t -> t
  val mem : M.key -> t -> bool
  val empty : t
end = struct
  type t = M.key M.t option

  let empty = Some M.empty
  let id_map = None

  let add k v = function
    | None -> failwith "Cannot add to infinite map"
    | Some w -> Some (M.add k v w)

  let q f k = Option.fold ~none:true ~some:(f k)
  let mem = q M.mem
  let l f k = Option.fold ~none:k ~some:(f k)
  let find = l M.find
end

module PPMap = IdMap (P.PathMap)

(**
   Before explaining this in detail, let's first review how we view recursive types.

   Before unfolding, suppose we have a recursive type Mu 'a.T. The collection of
   terminal locations in T together describe an "element" of the recursive type.
   Taking the view of recursive types being used for infinite data structures, all
   components then form a single element of that data structure. For example, if we have
   linked list, represented by Mu 'a.(int, 'a) ref then the null flag of the ref and the int
   value collectively form an element.

   During inference, we always operated on a one-level unfolding of a recursive type, i.e., an occurence
   of a mu binder must be under a ref constructor. So, returning to the list example, after a single
   unfolding we have (int, Mu 'a.[(int, 'a) ref]) ref. The element outside of the mu binder is called the head
   element; the intuition based on a linked list should provide some idea why. We also call
   the path to the above type the _root_ of a recursive type, as all unfoldings of the above
   type are related to the head element. In other words, recursive types are given their meaning
   with respect to some head element. The above unfolded type has a second element under the mu binder,
   we sometimes call this the summary element.

   Each element (under the mu binder or no) is represented by a [mu_frag] type, which is a fragment
   of the entire recursive type.

   A recursive refinement is represented with multiple components. The relationship between the
   concrete _head_ elements and all elements yielded by all future unfoldings of the type are
   represented in the monolithic program relation. Returning to our linked list example, we have
   that the value of the (concrete) integer in the head and all integer values in the tail/summary elements
   are given by R(hd, tl). In the case with multiple occurrences of a type variable, as in the case of a binary
   tree, the relationship is given by, e.g., R(hd, right, left), where _right_ represents all integer values reachable
   in the right sub tree, and left stands in for all values reachable in the left subtree.

   The above encoding only gives the relationship between the single, concrete head element and all values in
   child/tail/etc. elements. We also need to represent the relationship between the immediate
   children/successor/etc. of the head and the values reachable from their children, the relationship between those children, etc. etc.

   Representing this relationship is the role of the recursive mu_relations described above. Each mu binder in a type
   is associated with a relation between the element under that type and the elements given by a single unfolding of the recursive
   type. For example, let us consider the recursive type describing a binary tree:

   (hd: int, left: mu 'a.[(hd: int, 'a, 'a) ref], right: mu 'a.[(hd: int, 'a, 'a) ref]) ref

   The two mu binders for left and right are both associated with a relation.
   They represent the relationship between the _concrete_ elements underneath the mu binders (i.e., left->hd and right->hd)
   and the elements reachable via future unfoldings (i.e., left->left->hd, left->right->hd, left->left->hd, right->left->hd, etc.)

   Notice that with the above type representation, any concrete values for left->hd and right->hd are still hypothetical;
   currently, they are both still summarized under the mu binder. The recursive relations described above are
   used during unfolding, when fresh, concrete values are chosen for the (now concrete) right->hd and left->hd locations.
   This is discussed further in the documentation below.

   In short, recursive refinement is represented by a relation between concrete head elements and all elements
   yielded by unfolding, plus relations describing the relationship between the concrete values yielded by some
   unfolding and "future" values yielded by yet more unfolding.
*)
module RecursiveRefinements = struct
  type mu_frag = P.path * fltype
  (** a mu fragment. Represented by the path to an element (head or summary) and the type from that fragment. *)

  type rooted_mu = { hd : mu_frag; recurse : mu_frag P.PathMap.t }
  (** A complete representation of a recursive type. hd is the mu fragment of the head element, recurse is
     a map from paths to a mu fragment. It is not necessarily the case that the path used as a key into the map is
     the path in the mu fragment. In fact, almost (?) always the paths in the mu_frag will be a template
     path describing a path relative to the root of the recursive type to a mu binder. *)

  module Subst = struct
    let rec concr_arg_to_string = function
      | Ap p -> P.to_z3_ident p
      | BConst b -> Bool.to_string b
      | IConst i -> string_of_int i
      | KeyedChoice (p, a1, a2) ->
          Printf.sprintf "[? %s %s %s]" (P.to_z3_ident p)
            (concr_arg_to_string a1) (concr_arg_to_string a2)

    let to_string l =
      List.map
        (fun (p, a) -> Printf.sprintf !"%{P} |-> %s" p @@ concr_arg_to_string a)
        l
      |> String.concat "; " |> Printf.sprintf "[ %s ]"
    [@@ocaml.warning "-32"]
  end

  (** Generate a mu template based on a recursive type root, i.e., a
     reference type with the recursion flag set to true. The hd of the recursive
     type is a mu fragment whose path is the template type.


     The occurrences of the mu binders are both keyed by and represented
     in the mu_fragments by paths relative to the recursive type root.
  *)
  let to_mu_template ty =
    let recurse =
      walk_type ty
        (fun k ap ->
          match k with
          | `Summ -> `Cont ap
          | `Mu -> `K (fun ty acc -> (ap, ty) :: acc)
          | _ -> `Cont (path_step k ap))
        (fun _ acc -> acc)
        P.template []
    in
    let recurse =
      List.fold_left
        (fun acc (p, ty) -> P.PathMap.add p (p, ty) acc)
        P.PathMap.empty recurse
    in
    { hd = (P.template, ty); recurse }

  (**
     root a template created by the above at a concrete path. The keys in the recurse map remain
     relative to the root of the recursive type, but the paths in fragment are concretized with respect to the
     [path] argument.
  *)
  let root_template_at tmpl path =
    let root_frag (p, ty) = (P.root_at ~child:p ~parent:path, ty) in
    { hd = root_frag tmpl.hd; recurse = P.PathMap.map root_frag tmpl.recurse }

  (** Takes a series of indexed substitutions and generates the proper
     low-level relation argument substitutions. An indexed substitution
     generates conditional substitutions, where the symbolic name substituted
     for a relation argument is non-deterministically chosen by Z3. However,
     the substitutions generated here are such that if
     two substitutions are tagged with the the same index, then Z3
     must choose those two substitutions together.
  *)
  let to_multi_subst substs indexed_subst =
    fold_lefti
      (fun i acc sub_group ->
        let indexed_sub =
          List.fold_left
            (fun acc (ind, substs) ->
              List.fold_left
                (fun acc (s, d) ->
                  P.PathMap.update s
                    (fun curr ->
                      Some ((ind, d) :: Option.value ~default:[] curr))
                    acc)
                acc substs)
            P.PathMap.empty sub_group
        in
        let keyed_ap j = P.var @@ Printf.sprintf "star!%d!%d" i j in
        let to_unary_subst sorted =
          match sorted with
          | [] -> assert false
          | l ->
              let l = List.sort (fun (k1, _) (k2, _) -> k2 - k1) l in
              let _, hd = List.hd l in
              let tl = List.tl l in
              fold_lefti
                (fun i acc (_, ap) -> KeyedChoice (keyed_ap i, Ap ap, acc))
                (Ap hd) tl
        in
        P.PathMap.fold
          (fun s dlist acc -> (s, to_unary_subst dlist) :: acc)
          indexed_sub acc)
      (List.map lift_copy substs)
      indexed_subst

  (** Compute a substitution from the source fragment to the destination fragment.
     The generated substitution does NOT descend into mu binders so a substitution for
     a head element will not include tail elements.
     The skip ref flag indicates that the top level ref constructor should be skipped
     during substitution, and the substitution from src should begin under the ref
     constructor. This is used when generating a substitution from values in the
     head element into local variables (for unfolding), or vice versa (for folding).
  *)
  let compute_frag_subst ?(acc = []) ~skip_ref src_frag dst_frag =
    let ty, src, dst =
      if skip_ref then
        match snd src_frag with
        | `Ref (_, t) -> (t, P.deref @@ fst src_frag, fst dst_frag)
        | _ -> assert false
      else (snd src_frag, fst src_frag, fst dst_frag)
    in
    let ty = match ty with `Mu t -> t | _ -> ty in
    parallel_type_walk src dst ty
      (fun k _ () ->
        match k with
        | `Mu -> `K (fun _ acc -> acc)
        | `Summ | `Array | `Ref -> `Cont ())
      (fun () in_ap out_ap acc -> (in_ap, out_ap) :: acc)
      () acc

  (** Generate a substitution map for instantiating the arguments of a recursive relation
     with the concrete paths used in unfolding *)
  let compute_mu_template_subst { hd = path, ty; _ } =
    parallel_type_walk P.template path ty
      (fun _ _ () -> `Cont ())
      (fun () in_ap out_ap acc -> (in_ap, Ap out_ap) :: acc)
      () []

  (** Compute a multi subst from the source template to the given head fragment
     and tail fragments. The substitution of the head element is made with respect to
     the the hfrag. The subsitutiion for the tail elements
     is determined by the [tl] map; it maps from a (relative) path to each mu binder
     in [src_templ] to a list of fragments to be multi-substituted into that place.
     In other words, a substitution is generated such that Z3 nondeterministically
     chooses symbolic name from one of the possibilities in the tail map.
     However, by virtue of the mutli subst, if the choice is made for one path in
     in target fragment a, all other paths under the same binder will choose
     their symbolic name from a as well.
  *)
  let compute_mu_multi_subst ?(skip_hd_ref = false) src_templ ~hd:hfrag
      ~tl:tfrags =
    let subst = compute_frag_subst ~skip_ref:skip_hd_ref src_templ.hd hfrag in
    let indexed_subst =
      P.PathMap.fold
        (fun bind_path src_frag acc ->
          let dst_frags = P.PathMap.find bind_path tfrags in
          let sub_group =
            fold_lefti
              (fun i acc dst_frag ->
                let s = compute_frag_subst ~skip_ref:false src_frag dst_frag in
                (i, s) :: acc)
              [] dst_frags
          in
          sub_group :: acc)
        src_templ.recurse []
    in
    to_multi_subst subst indexed_subst

  (** Compute mu substitution sourc template to the hd mu fragment given by [hd].
     The choice of target for the tail fragments is given by the [tl] map argument,
     which is keyed by the relative path to the mu binder in the source template.
  *)
  let compute_mu_subst src_templ ~hd:hfrag ~tl:tfrags =
    let subst = compute_frag_subst ~skip_ref:false src_templ.hd hfrag in
    P.PathMap.fold
      (fun path src_frag acc ->
        let dst_frag = P.PathMap.find path tfrags in
        compute_frag_subst ~skip_ref:false ~acc src_frag dst_frag)
      src_templ.recurse subst
    |> List.map lift_copy

  (** Generate a substitution for a type, starting at src and dst, but not descending
   under mu binders *)
  let partial_subst src dst ty =
    parallel_type_walk src dst ty
      (fun k _ () ->
        match k with `Mu -> `K (fun _ acc -> acc) | _ -> `Cont ())
      (fun () in_ap out_ap acc -> (in_ap, out_ap) :: acc)
      () []

  let relation_subst rel subst = PRelation (rel, subst, None)

  (** Here we go!

     Some background. [root] is path to the root type of the recursive type, i.e., the type
     at the root of the recursive type. target is the path to which the unfolded
     type information should be transferred. All substitutions are made with respect
     to [target], before generation the result paths are pre-processed
     with [out_mapping]. This greatly simplifies the implementation to handle
     unfolding which has a tuple pattern as the LHS; we unfold with respect to a
     dummy root variable, and then translate from the dummy paths into the output
     paths. Note that if a result path does not appear in out_mapping, it is
     ommitted from the substitution. We refer to finding the final result of a substitution
     (or omitting it) "normalization".

     Note that the target path is assumed to point to a variable of type T, where root
     is of type ref T; i.e., target is assumed to hold the contents of root (after unfolding).

     The [with_havoc] flag determines if the assignment represented by the unfolding
     should be treated as an ownership operation. This is almost always true,
     with the exception of the dummy unfolding used by the aliasing operation. See
     that code for details.
  *)
  let unfold_to ~with_havoc ?(out_mapping = PPMap.id_map) ~e_id ref_ty root
      target in_rel out_rel ctxt =
    (* Normalize the paths to be havoced/stabilized *)
    let normalize_ap p =
      if PPMap.mem p out_mapping then PPMap.find p out_mapping else p
    in
    let normalize_havoc pset = P.PathSet.map normalize_ap pset in
    (* Normalize a substitution, walking into keyed choices as necessary *)
    let rec deep_normalize = function
      | Ap p -> Ap (normalize_ap p)
      | BConst c -> BConst c
      | IConst i -> IConst i
      | KeyedChoice (p, a1, a2) ->
          KeyedChoice (normalize_ap p, deep_normalize a1, deep_normalize a2)
    in
    let normalize_subst subst =
      List.map (fun (s, d) -> (s, deep_normalize d)) subst
    in

    (* The type under the ref *)
    let cont_ty = match ref_ty with `Ref (_, t) -> t | _ -> assert false in

    let source_path = root in
    let template = to_mu_template ref_ty in
    let source_mu = root_template_at template source_path in
    let target_path = target in

    (* We unfold the relation input R(hd, tl) for a recursive linked list type as follows:

       R(hd, tl!pass) /\ R(hd, tl) /\ R(hd, tl->tl) /\ hd(tl, tl->tl) => Q(hd, tl!pass, hd, tl, tl->tl)
       hd(x,y) => tl(x, y)

       R here encodes a relationship between hd and all tail elements, i.e. elements reachable from the tail pointer of hd.
       Thus, in the precondition, R is used to relate tl, the (concrete) value chosen as the
       new head element yielded by unfolding, and tl->tl, the (summary) value representing
       all values reachable from tl. The relationship between tl and all values reachable
       from its tail pointer is encoded with an application of hd(tl, tl->tl). Here hd encodes
       the recursive refinement.

       Notice that we've said that the "pointwise" relationship between tl and all "further"
       element is the same relationship that holds between all further heads and their
       successors (hd => tl).

       NB: the weak copy from tl to the new concrete head.

       For a more complicated example, let us consider the unfolding of the sorted tree type.

       We have:
       (hd:int, left: mu (hd:int, 'a, 'a), left: mu (hd:int, 'a, 'a)

       The type variable bindings and ref constructors are omitted to save space.

       After unfolding, there will be two new summary locations under left and right,
       and one new concrete location under the same. The input relation is:

       R(hd, left->hd, right->hd)

       When unfolding we generate the following preconditions:
       R(hd, left->hd, right->hd) /\
       R(hd, left->left->hd, right->hd) /\
       R(hd, left->right->hd, right->hd) /\
       R(hd, left->hd, right->right->hd) /\ ...

       That is, all possible combinations of substitutions for values (concrete or summary)
       underneath the right and left labels in the source type. (A good question is why
       we don't use the multi subst here, the answer is: I don't actually remember. I did
       use it originally, but something about it didn't work. A mystery for you, dear reader,
       to solve.)

       Then, we relate the new head locations (right->hd and left->hd) to the new summary
       locations with the respective recursive refinements:
       right(right->hd, right->left->hd, right->right->hd) and
       left(left->hd, left->left->hd, left->right->hd)

       The recursive refinements have been named by the symbolic name of their mu binder location.

       The result is als follows:

       Q(hd, right->hd!pass, left->hd!pass, right->hd, right->left->hd, right->right->hd,
         left->hd, left->left->hd, left->right->hd)

       (with the null flags omitted). The recursive refinements are propagated as well:
       right => right->right
       right => right->left
       left => left->right
       left => left->left
    *)

    (* After unfolding, the location of the mu binders in the source type will become
       roots of recursive type instances. These recursive type isntances will have exactly
       the same type/structure as the source type being unfolded. This walks the content type
       and generates a mu map, which is an association list from the relative paths of the
       mu binders in the source type to the (concrete) output paths that will hold the unfolding
       of those mu binders. *)
    let mu_mapping =
      parallel_type_walk (P.deref @@ P.template) target_path cont_ty
        (fun k (in_ap, out_ap) () ->
          match k with
          | `Mu ->
              `K (fun _ acc -> (in_ap, root_template_at template out_ap) :: acc)
          | _ -> `Cont ())
        (fun _ _ _ acc -> acc)
        () []
    in

    (* We now compute the R(hd, tl) /\ R(hd, tl->tl) and R(hd, left->hd, right->hd) /\ ...
       substitution. The unfolding mu type here gives, for each mu binder in the source type,
       the set of mu fragments corresponding to each element under that binder, i.e.,
       the newly concretized head and the (new) tail elements.*)
    let unfolding_mu =
      List.fold_left
        (fun acc (src_mu, target_mu) ->
          (* The target mu hd, and all possible fragments under all binders *)
          let l =
            target_mu.hd
            :: (P.PathMap.bindings target_mu.recurse |> List.map snd)
          in
          P.PathMap.add src_mu l acc)
        P.PathMap.empty mu_mapping
    in

    let rec combination_loop l =
      match l with
      | [] -> [ P.PathMap.empty ]
      | (src_mu, possibilities) :: t ->
          let comb = combination_loop t in
          ListMonad.bind
            (fun mu -> List.map (fun m -> P.PathMap.add src_mu mu m) comb)
            possibilities
    in
    let combinatorial_subst =
      P.PathMap.bindings unfolding_mu
      |> combination_loop
      (* Ultimately this yields a list of substitutions, each of which has a different possible
         choice for element under a binder *)
      |> List.map (fun m ->
             (* Why the head? because this substitution is applied in the precondition, so we
                want the relationship to be w.r.t the (concrete) source head elements) *)
             compute_mu_subst source_mu ~hd:source_mu.hd ~tl:m)
    in

    let recursive_substs =
      List.map
        (fun (in_ap, out_mu) ->
          (* get the relation for the source mu binder, and then generate a substition to
             instantiate the arguments of the recursive refinement with the newly concrete
             head generated by the unfolding of the source binder and the new tail elements *)
          let rel =
            P.PathMap.find
              (P.root_at ~child:in_ap ~parent:source_path)
              ctxt.recursive_rel
          in
          (rel, compute_mu_template_subst out_mu))
        mu_mapping
    in

    (* These are the DIRECT flow from the concrete head to whatever output exists. Thus, we do
       an output substitution map, as it's fine (and even necessary) for Z3 to infer
       equality between the concrete head and the result of unfolding. *)
    let output_flows =
      partial_subst (P.deref source_path) target_path cont_ty
      |> List.map (fun (s, d) -> (normalize_ap d, Ap s))
    in

    (* now compute the havocs (if requested) *)
    let all_havocs =
      if with_havoc then
        (* Here we directly track the ownership status of the containing paths rather
           than retraversing a path at each terminal location in the path.
           In addition, this allows us to track the havoc states under a mu binder
           to determine if the mu relation must be havoced (see the Havoc documentation
           and RecRelations module documentation for how we represent that havoc state) *)
        parallel_type_walk (P.deref @@ source_path) target_path cont_ty
          (fun k (in_ap, out_ap) (ih, oh, parent_mu) ->
            match k with
            | `Summ -> failwith "Impossible?"
            (* When passing under a mu binder, switch to tracking paths relative to the mu binder;
               this makes computing the mu path to havoc much easier (we save the concrete
               input paths to make reconstructing the source path trivial). Note that whether the
               third element of the state is None or Some _ determines whether we are under a mu
               binder. *)
            | `Mu ->
                `ContPath
                  (P.template, P.template, (ih, oh, Some (in_ap, out_ap)))
            | `Ref | `Array ->
                let concr_path =
                  Option.fold ~none:in_ap
                    ~some:(fun (src, _) -> P.root_at ~child:in_ap ~parent:src)
                    parent_mu
                in
                let ih, oh =
                  OI.SplitMap.find
                    (OI.SBind e_id, concr_path)
                    ctxt.o_hints.OI.splits
                in
                `Cont (ih = 0.0, oh = 0.0, parent_mu))
          (fun (ih, oh, parent_mu) in_ap out_ap acc ->
            match parent_mu with
            | None ->
                (* then we have not reached the mu binder yet, these are all direct copies *)
                H.add_havoc in_ap ih @@ H.add_havoc out_ap oh acc
            | Some (mu_ap, dst_root_ap) ->
                (* Get the concrete paths *)
                let in_path = P.root_at ~child:in_ap ~parent:mu_ap in
                let out_hd = P.root_at ~child:out_ap ~parent:dst_root_ap in
                let acc =
                  H.add_havoc out_hd oh acc |> H.add_havoc in_path ih
                  |> H.add_mu_havoc ~binder:mu_ap ~ty:ref_ty in_ap ih
                in
                (* However, if we havoc in the unfolding, then the mu element havoc
                   must be given with respect to the (new) location of the binders in
                   the unfolding (recall that the mu_ap is the mu binder in the source
                   type, and the dst_root_ap is now the root of a recursive type. so
                   below we compute the new (absolute) paths of the mu binders in the unfolded
                   type, and set the havoc state with respect to those binders.
                *)
                RecRelations.get_mu_binders P.template ref_ty
                |> List.fold_left
                     (fun acc binder ->
                       let binder =
                         normalize_ap
                         @@ P.root_at ~child:binder ~parent:dst_root_ap
                       in
                       H.add_mu_havoc ~binder ~ty:ref_ty out_ap oh acc)
                     acc)
          (false, false, None) H.empty_havoc_state
      else H.empty_havoc_state
    in

    let all_havocs =
      { all_havocs with havoc = normalize_havoc all_havocs.havoc }
    in

    let rec_havocs = H.to_rec_havoc all_havocs in
    (* Here we generate the hd => tl or right => right->right implications *)
    (* Again, due to duplication, under each mu binder in the source, we compute the
       new locations of the mu binders in the (unfolded) output, and copy the
       binder from the source to the target. Note that if the output binder
       does not actually appear in the normalization map, no copying takes place *)
    let ctxt =
      List.fold_left
        (fun ctxt (binder_path, target_mu) ->
          let source_mu = P.root_at ~child:binder_path ~parent:source_path in
          let src_rel = P.PathMap.find source_mu ctxt.recursive_rel in
          let ctxt =
            copy_rel ~by_havoc:rec_havocs ~e_id src_rel ~ty:ref_ty source_mu
              ctxt
          in
          let dst_root = fst target_mu.hd in
          RecRelations.get_mu_binders P.template ref_ty
          |> List.fold_left
               (fun ctxt binder ->
                 let target_mu = P.root_at ~child:binder ~parent:dst_root in
                 if PPMap.mem target_mu out_mapping then
                   let target_mu = PPMap.find target_mu out_mapping in
                   copy_rel ~by_havoc:rec_havocs ~e_id ~ty:ref_ty src_rel
                     target_mu ctxt
                 else ctxt)
               ctxt)
        ctxt mu_mapping
    in

    let pre_flows =
      [
        rel ~ty:ZBool
        @@ mk_relation (Ap (P.to_null source_path)) "=" (BConst is_nonnull_flag);
        relation_subst in_rel [];
      ]
      @ List.map
          (fun (rel, subst) -> PRelation (rel, normalize_subst subst, None))
          recursive_substs
      @ List.map
          (fun subst -> PRelation (in_rel, normalize_subst subst, None))
          combinatorial_subst
    in
    let output_subst = augment_havocs output_flows all_havocs.havoc in

    let unfold_impl =
      ( pre_flows @ null_pre out_rel output_subst,
        PRelation (out_rel, output_subst, None) )
    in
    let havoc_set = P.PathSet.union ctxt.havoc_set all_havocs.havoc in
    {
      ctxt with
      impl = unfold_impl :: ctxt.impl;
      havoc_set;
      omit_set =
        merge_havoc_omit (get_relation_ident out_rel) havoc_set ctxt.omit_set;
    }

  type ap_subst = (P.concr_ap * P.concr_ap) list

  (* This copy policy will be documented as soon as I remember how on earth it works *)
  type copy_policy =
    | Weak
    | Custom of {
        rename_src : ap_subst;
        rename_weak : ap_subst;
        rename_out : ap_subst;
      }

  (**
     Folds the path pointed to by target_root into the recursive type rooted at src_root. The [target_root] should have type [ref_ty] which is a root of a recursive
     type, i.e., a reference type constructor with the recursion flag set to true. The source root meanwhile, should refer to a type which is the _content type_
     of ref_ty after a one level unfolding of the recursive types in ref_ty.

     The havoc status of the paths before and after folding are determined by the oracle
     argument. havoc_ext is an optional function for extending the computed
     havoc state. It is used in the aliasing.

     [rec_ext] is an (optional) map from mu binders in the destination to "recursive
     implication extensions". These recursive implication extensions are applied when
     the recursive refinement is being generated for the mu binder at the given path.

     An extension is a 2-ary tuple where the first element is a substitution to apply
     when generating the implication for the head element and the immeidate successors.
     Thus, it can turn R(hd, tl, x) => hd(hd, tl) into R(hd, tl, hd) => hd(hd, tl). This
     is used when you know some other symbolic variable in scope must have the same
     value as these arguments, i.e., during an alias.

     The second element is a map concrete paths mu binders in the destination to a list
     of clauses. This is used if you know that the invariants satisfied by a mu binder in the
     source type must be also satisfy another relationsio, i.e., again during aliasing.
  *)
  let fold_to ~oracle:(dst_oracle, src_oracle) ~e_id ~copy_policy ?rec_ext
      ?havoc_ext ref_ty (src_root : P.concr_ap) (target_root : P.concr_ap)
      in_rel out_rel ctxt =
    let src_ap = src_root in
    (* The content type. The type of target_root should be the result of a deep_type_normalization of this *)
    let cont_ty = match ref_ty with `Ref (_, t) -> t | _ -> assert false in
    let mu_template = to_mu_template ref_ty in
    let target_ap = target_root in
    let target_mu = root_template_at mu_template target_root in
    (* This mu map in some sense inverts the role served by the similarly named variable in the unfold function.

       This produces a map from (relative) mu binders paths to the roots of [unfolded] types to be folded into the
       given mu binder.

       For example, suppose we want to fold (x, (hd, tl)) into (hd', mu (tl', 'a)). Then we have to
       generate the constraint:

       R(x, hd, tl) => Q(x, [? hd' tl'])

       In otherwise, the (currently) concrete head element is collapsed with its own summary pieces.
       As a result any relation Q(x, tl'') derived by Z3 must be a relationship that holds between x and hd, and
       between x and any values reachable from hd's tail, i.e. tl. This matches the intuition given for the representation
       of recursive refinements given in unfold.
    *)
    let mu_map =
      parallel_type_walk (P.deref @@ P.template) src_root cont_ty
        (fun k (in_ap, out_ap) () ->
          match k with
          | `Mu ->
              `K
                (fun _ acc ->
                  (in_ap, root_template_at mu_template out_ap) :: acc)
          | _ -> `Cont ())
        (fun () _ _ acc -> acc)
        () []
    in

    (* This associates with each mu binder identifying a summary element in the folded target the elements (concrete and
       otherwise) in the unfolded source. *)
    let fold_up_map =
      List.fold_left
        (fun acc (out_binder, input_mu) ->
          let l =
            input_mu.hd :: (P.PathMap.bindings input_mu.recurse |> List.map snd)
          in
          P.PathMap.add out_binder l acc)
        P.PathMap.empty mu_map
    in

    (* This generates a multi substitution; the head element is given by the (conrete) elements reachable from the src ap *)
    let fold_up_subst =
      compute_mu_multi_subst ~skip_hd_ref:true target_mu ~hd:(src_ap, cont_ty)
        ~tl:fold_up_map
    in

    (* Determines how the copying of the tail elements from the input relation to the output. By default,
       the strategy is to weakly copy the summary locations from the source mu binders to the output.

       Returning to the example above, assuming x, hd, and tail do not go out of scope, we will actually have
       R(x, hd, tl) /\ R(x, hd, tl!pass) => Q(x, hd, tl!pass, x, [? hd tl])
    *)
    let rename_src, rename_weak, rename_out =
      match copy_policy with
      | Weak ->
          let weak =
            ListMonad.bind
              (fun (_, mu) ->
                compute_copies (fst mu.hd) (fst mu.hd) (snd mu.hd)
                |> to_copy_stream
                |> List.filter_map (fun (a, b, k) ->
                       if k = `Direct then None else Some (a, to_pass_ap b)))
              mu_map
          in

          ([], weak, weak)
      | Custom { rename_src; rename_weak; rename_out } ->
          (rename_src, rename_weak, rename_out)
    in

    (* handles a terminal locations. Look up the concrete path in the given havoc oracle.
       The state is a mu chain which is managed by the MuChain.raw_stepper. By the invariant, the optional mu
       path is Some only when under a mu binder; when it is we also update the mu havoc.
    *)
    let handle_term oracle st acc =
      let full_path = RecRelations.MuChain.to_concr st in
      let flg = oracle full_path in
      let acc = H.add_havoc full_path flg acc in
      Option.fold ~none:acc ~some:(fun (p, binder) ->
          H.add_mu_havoc ~binder ~ty:ref_ty p flg acc)
      @@ RecRelations.MuChain.get_mu_path st
    in
    let hstate =
      walk_type cont_ty RecRelations.MuChain.raw_stepper
        (handle_term dst_oracle)
        (P.deref target_root, None)
        H.empty_havoc_state
      |> walk_type
           (deep_type_normalization cont_ty)
           RecRelations.MuChain.raw_stepper (handle_term src_oracle)
           (src_ap, None)
    in

    let by_havoc = H.to_rec_havoc hstate in
    (* Now we compute the recursive refinements for the new mu binders *)
    let ctxt =
      List.fold_left
        (fun ctxt (dst_binder, src_folded) ->
          (* The absolute path of the output mu binder *)
          let target_mu = P.root_at ~child:dst_binder ~parent:target_ap in
          (* rel is the new element *)
          let ctxt, rel =
            RecRelations.recursive_rel_for ~e_id ref_ty target_mu ctxt
          in
          let with_havoc ante ctxt =
            RecRelations.impl_with_havoc ~ante ~by_havoc target_mu rel ctxt
          in
          let hd_subst, conj_ind =
            Option.bind rec_ext (P.PathMap.find_opt dst_binder)
            |> Option.value ~default:([], P.PathMap.empty)
          in
          let ctxt =
            (* Get the absolute paths of the mu binders under the recursive type
               being folded into mu binders rooted at target_mu *)
            RecRelations.get_mu_binders (fst src_folded.hd) (snd src_folded.hd)
            |> List.fold_left
                 (fun ctxt mu_path ->
                   (* for each such path, get the relation describing the
                      relationship under the mu binder *)
                   let input_rec = P.PathMap.find mu_path ctxt.recursive_rel in
                   let input_rec = PRelation (input_rec, [], None) in
                   (* we also grab an optional recursive relation as specified by the conj_ind which
                      itself was read from the rec_ext. *)
                   (* add that any relationship admitted by this "sub" mu relation is admitted by
                      the folded relation. *)
                   let ante =
                     input_rec
                     :: (Option.to_list @@ P.PathMap.find_opt mu_path conj_ind)
                   in
                   (* with havoc applies the implication describe above, providing all the
                      necessary common arguments to impl_with_havoc *)
                   with_havoc ante ctxt)
                 ctxt
          in
          (* in addition, say that the relationship between the (to be folded) head
             and it's successor/tail elements (as described by the monolithic relation) are
             also admitted by the new recursive relation *)
          let subst =
            compute_mu_template_subst src_folded
            |> List.map (function
                 | src, Ap dst -> (dst, Ap src)
                 | _ -> assert false)
          in
          with_havoc [ PRelation (in_rel, subst @ hd_subst, None) ] ctxt)
        ctxt mu_map
    in
    (* as in the unfold, copy the mu binders from the source to themselves; this copy
       is necessary to havoc the input relations *)
    let ctxt =
      List.fold_left
        (fun ctxt (_, src_folded) ->
          RecRelations.get_mu_binders (fst src_folded.hd) (snd src_folded.hd)
          |> List.fold_left
               (fun ctxt src_mu ->
                 let src_rel = P.PathMap.find src_mu ctxt.recursive_rel in
                 copy_rel ~by_havoc ~e_id ~ty:ref_ty src_rel src_mu ctxt)
               ctxt)
        ctxt mu_map
    in

    let hstate =
      match havoc_ext with
      | Some f ->
          let havoc, stable = f ~havoc:hstate.havoc ~stable:hstate.stable in
          { hstate with havoc; stable }
      | None -> hstate
    in
    let havoc_set =
      P.PathSet.union hstate.havoc
      @@ P.PathSet.diff ctxt.havoc_set hstate.stable
    in

    let output_flows flow_subst =
      augment_havocs (flow_subst @ List.map lift_copy rename_out) havoc_set
    in
    let ante =
      [
        PRelation (in_rel, List.map lift_copy rename_weak, None);
        rel ~ty:ZBool
        @@ mk_relation (Ap (P.to_null target_root)) "=" (BConst is_nonnull_flag);
        PRelation (in_rel, List.map lift_copy rename_src, None);
      ]
    in
    let fold_impl =
      let flows = output_flows fold_up_subst in
      let null_ante = null_pre out_rel fold_up_subst in
      let conseq = relation_subst out_rel flows in
      (ante @ null_ante, conseq)
    in
    {
      ctxt with
      impl = fold_impl :: ctxt.impl;
      havoc_set;
      omit_set =
        merge_havoc_omit (get_relation_ident out_rel) havoc_set ctxt.omit_set;
    }
end

(* ty is the type of the src variable (including the reference constructor *)
let%lm do_unfold_copy ~with_havoc ?(out_mapping = PPMap.id_map) ~e_id src_var
    dst_var (ref_ty : fltype) in_rel out_rel ctxt =
  RecursiveRefinements.unfold_to ~e_id ~with_havoc ~out_mapping ref_ty
    (P.var src_var) (P.var dst_var) in_rel out_rel ctxt

(* folded ty is the type under the reference after the fold, i.e., the
   type of in_ap after folding.
   out_ap is under a ref, i.e. the location in memory where we are folding to.
*)
let%lm do_fold_copy ~e_id in_ap out_ap folded_ty in_rel out_rel ctxt =
  let dst_oracle = havoc_oracle ctxt (OI.MGen e_id) in
  let ctxt, so = split_oracle (OI.SBind e_id) ctxt in
  let src_oracle p =
    let f1, _ = so p p in
    f1 = `Havoc
  in
  RecursiveRefinements.fold_to ~oracle:(dst_oracle, src_oracle) ~e_id
    ~copy_policy:RecursiveRefinements.Weak folded_ty (P.var in_ap)
    (P.var out_ap) in_rel out_rel ctxt

let apply_identity_flow ?pre = add_relation_flow ?pre []

let const_assign lhs const in_rel out_rel =
  let%bind havoc_state = get_havoc_state in
  let flows =
    P.PathSet.elements havoc_state
    |> List.fold_left (fun acc p -> Havoc p :: acc) [ Const (lhs, const) ]
  in
  add_relation_flow flows in_rel out_rel
  >> set_havoc_state ~rel:(get_relation_ident out_rel) havoc_state

let vderef v = P.deref @@ P.var v

(** This simply determines whether a path needs a pre version.
   Constant locations do not need a pre version *)
let rec is_pre_path p =
  match P.tail p with
  | None -> false
  | Some `Deref -> true
  | Some `Len | Some (`Proj _) -> is_pre_path @@ P.parent p
  | Some _ -> false

(** the mega argument tuple records the following information
   + the access paths havoced after the call
   + the access paths stable after the call
   + the argument substitutions to apply to the function input relations
   + the argument substitutions to apply to the function output relation
   + the substitutions to apply to the call substitution, which is used in
   the output to compute in/out summaries (see below)

   actual is the path of the argument, formal is the path of the argument.
*)
let bind_arg ~fn ~cid ~e_id (havoc, stable, in_bind, out_bind, pre_bind) actual
    formal ty =
  let copies = compute_copies actual formal ty in
  let direct_copies = to_copy_stream copies in
  let%bind split_oracle = split_oracle (SCall e_id) in
  let%bind fun_info = get_function_info fn in

  (* Here we compute the set of ID paths, i.e., paths
     that must NOT change during execution of the function. These
     are access paths that are not havoced by splitting the argument.
     We exploit this to conclude that the value before/after execution must be unchanged,
     giving extra precision.
  *)
  let hstate =
    List.fold_left
      (fun acc (src, dst, k) ->
        let havoc, dst_havoc = split_oracle src dst in
        let acc =
          match k with
          | `Mu (under_mu_path, _, dst_binder, ty) ->
              (* here we save whether the destination for the mu relation is to be havoced.
                 This is used when we perform the implication for mu_relations into
                 the function; we have to havoc those explicitly during the implication.
              *)
              H.add_mu_havoc ~ty ~binder:dst_binder under_mu_path
                (dst_havoc = `Havoc) acc
          | _ -> acc
        in
        H.add_havoc src (havoc = `Havoc) acc)
      H.empty_havoc_state direct_copies
  in
  let id_paths = hstate.H.stable in

  (* Here we generate the substitution maps for the functions input relations. For
     input arguments that are direct (not weak) copies and which are pre paths (Those
     in mutable storage) are also substituted as pre paths.

     To explain pre paths:
     To track input and output behavior, we introduce shadow values that
     represent the values of all mutable, concrete locations at function entry. These
     are treated as dummy variables that are totally opaque to the program, but which are
     threaded through with the rest of the state.

     For a function which mutates a pointer argument, we will have f-in(x->*, x->*!pre)
     representing the value of x->* at method entry, which is tranformed, interrogated, etc.
     by the function, and the pre path x->*!pre which is equal to x->* at entry, but is
     immutable through program execution.

     Accordingly, when generating the input relation substitutions, if the formal
     argument is y we would generate the substitution [y->*/x->*;y->*/x->*!pre].
  *)
  let in_bind =
    List.fold_left
      (fun in_bind (src, dst, k) ->
        let in_bind = (dst, Ap src) :: in_bind in
        if is_pre_path src && k = `Direct then (P.pre dst, Ap src) :: in_bind
        else in_bind)
      in_bind direct_copies
  in

  let%bind havoc_out_oracle = gen_oracle (OI.MOut fn) in

  (* dst is the access path for the argument *)
  let havoc, stable, out_bind, pre_bind =
    List.fold_left
      (fun (havoc, stable, out_bind, pre_bind) (src, dst, k) ->
        let is_pre = is_pre_path src && k = `Direct in
        let is_id = P.PathSet.mem src id_paths in
        (* just because the output path is havoced, if we have some residual ownership
           in the argument path, then the value itself is immutable and NOT havoced *)
        let havoc_out = havoc_out_oracle dst && not is_id in
        let havoc, stable =
          if havoc_out then (P.PathSet.add src havoc, stable)
          else (havoc, P.PathSet.add src stable)
        in

        let out_copy = (dst, Ap src) in
        let pre_path = P.map_root (fun p -> p ^ "!call") src in
        let pre_copy = (src, Ap pre_path) in

        (* to understand what's happening below, let the input state with a single argument x be IN(x).
           The successour state is SUCC(x) and the output predicate is OUT. OUT may (or may not) have
           a pre argument, with formal names $0 and $0!pre *)

        (* now compute the out flows, let's do the easy case first *)
        if (not is_pre) && is_id then
          (* Then this is an argument that may not change during execution and for which we do not track
             pre-states then no pre-substitutions are necessary *)

          (* Then we want to do the following IN(x) /\ OUT(x) => SUCC(x), i.e. the values are all the same.
             out copy is $0 -> x *)
          (havoc, stable, out_copy :: out_bind, pre_bind)
        else if not is_pre then
          (* this argument may change during execution, and we do not track pre-states. Then create a fresh
             name for the input value (using pre) *)

          (* Then we have IN(x') /\ OUT(x) => SUCC(x). Pre_copy here renames x in IN to x'
             and out_copy is $0 -> x' *)
          (havoc, stable, out_copy :: out_bind, pre_copy :: pre_bind)
        else if is_pre && is_id then
          (* we track pre states but the argument won't change during execution.
             So constrain the pre-value to be equal to the output argument (do not rename pre) *)

          (* Then we have IN(x) /\ OUT(x,x) => SUCC(x) out_copy is as above, and the second substitution gives $0!pre -> x *)
          (havoc, stable, (P.pre dst, Ap src) :: out_copy :: out_bind, pre_bind)
        else
          (* finally, we track pre states, and the value may change.
             rename the name in the prestate to be pre,
             and rename the pre path in the output *)

          (* Then we have IN(x') /\ OUT(x, x') => SUCC(x)

             Our out substitutions are $0!pre -> x' and $0 -> x, and our precopy renames x in IN to x' *)
          ( havoc,
            stable,
            (P.pre dst, Ap pre_path) :: out_copy :: out_bind,
            pre_copy :: pre_bind ))
      (havoc, stable, out_bind, pre_bind)
      direct_copies
  in
  let mu_copy = to_mu_copies copies in
  let%lm update_in_rel susp (_, src_mu, dst_mu, _) ctxt =
    let ctxt, () = susp ctxt in
    let in_rel = P.PathMap.find src_mu ctxt.recursive_rel in
    let out_rel = P.PathMap.find dst_mu fun_info.in_recursive_rel in
    RecRelations.impl_with_havoc ~out_shift:cid ~by_havoc:hstate.mu_havoc
      ~ante:[ PRelation (in_rel, [], None) ]
      dst_mu out_rel ctxt
  in
  let%bind () = List.fold_left update_in_rel (return ()) mu_copy in
  let%lm update_out_rel susp (_, src_mu, dst_mu, ty) ctxt =
    let ctxt, () = susp ctxt in
    let out_rel = P.PathMap.find dst_mu fun_info.out_recursive_rel in
    (* Note: we don't try to use information from the source relation. It's really
       hard and annoying to figure out which paths are havoced and what not. *)
    (* TODO: maybe we should conjoin if the paths are not ownership havoced. This is *really*
       hard and annoying *)
    let ctxt, result_rel =
      RecRelations.recursive_rel_for ~e_id ty src_mu ctxt
    in
    {
      ctxt with
      impl =
        ([ PRelation (out_rel, [], Some cid) ], PRelation (result_rel, [], None))
        :: ctxt.impl;
    }
  in
  let%bind () = List.fold_left update_out_rel (return ()) mu_copy in
  return (havoc, stable, in_bind, out_bind, pre_bind)

(* Bind the return w.r.t some pattern. Fairly straighforward if you read the above *)
let bind_return ~fn ~e_id ~cid out_patt ret_type =
  let copies = compute_patt_copies P.ret out_patt ret_type in
  let direct_copies = to_copy_stream copies in
  let%bind havoc_oracle = gen_oracle @@ MRet fn in
  let havoc_ret =
    List.fold_left
      (fun acc (src, dst, _) ->
        if havoc_oracle src then P.PathSet.add dst acc else acc)
      P.PathSet.empty direct_copies
  in
  let%bind fun_info = get_function_info fn in
  let%bind () =
    List.fold_left
      (fun m_unit (_, src_mu, dst_mu, ty) ctxt ->
        let ctxt, () = m_unit ctxt in
        let ctxt, rel = RecRelations.recursive_rel_for ~e_id ty dst_mu ctxt in
        let return_rel = P.PathMap.find src_mu fun_info.out_recursive_rel in
        ( {
            ctxt with
            impl =
              ( [ PRelation (return_rel, [], Some cid) ],
                PRelation (rel, [], None) )
              :: ctxt.impl;
          },
          () ))
      (return ()) (to_mu_copies copies)
  in
  return (List.map (fun (s, d, _) -> (s, Ap d)) direct_copies, havoc_ret)

(** Get a list of arguments for function [fn_name] *)
let%lq find_params fn_name ctxt = SM.find fn_name ctxt.fn_params

let bind_args ~e_id out_patt call_expr curr_rel body_rel =
  let callee = call_expr.callee in
  let%bind callee_type = get_function_type callee in
  let%bind in_rel = get_in_relation callee in
  let%bind out_rel = get_out_relation callee in
  let args = call_expr.arg_names in
  let%bind havoc, stable, in_bindings, out_bindings, pre_bindings =
    fold_left2i
      (fun i acc arg_name arg_ty ->
        let%bind acc = acc in
        bind_arg ~fn:callee ~cid:call_expr.label ~e_id acc (P.var arg_name)
          (P.arg i) arg_ty)
      (return (P.PathSet.empty, P.PathSet.empty, [], [], []))
      args callee_type.arg_types
  in
  let%bind return_bindings, havoc_bind =
    bind_return ~fn:callee ~e_id ~cid:call_expr.label out_patt
      callee_type.ret_type
  in
  let%bind havoc_state = get_havoc_state in
  let havoc_state =
    P.PathSet.union havoc_bind
    @@ P.PathSet.union (P.PathSet.diff havoc_state stable) havoc
  in

  let havoc_subst =
    P.PathSet.elements havoc_state
    |> List.mapi (fun i p -> (p, Ap (havoc_ap i p)))
  in
  [%m
    add_implication [ PRelation (curr_rel, [], None) ]
    @@ PRelation (in_rel, in_bindings, Some call_expr.label);
    add_implication
      [
        (* the copy of the pre relation, which is used to provide information about the
           relationships of the values at input which are the values of the pre arguments *)
        PRelation (curr_rel, pre_bindings, None);
        PRelation (out_rel, return_bindings @ out_bindings, Some call_expr.label);
      ]
    @@ PRelation (body_rel, havoc_subst, None);
    set_havoc_state ~rel:(get_relation_ident body_rel) havoc_state]

let process_intrinsic out_patt call_expr intr_type curr_rel body_rel =
  (* check pre-conditions *)
  (* TODO: factor this out *)
  let arg_names =
    fold_lefti
      (fun i acc arg -> StringMap.add (P.arg_name i) arg acc)
      StringMap.empty call_expr.arg_names
  in
  let type_fail () =
    failwith @@ "Cannot handle non-integer typed args in built in functions: "
    ^ call_expr.callee
  in
  let%bind () =
    miteri
      (fun i t ->
        let nu_arg = P.var (List.nth call_expr.arg_names i) in
        match t with
        | RT.Int r ->
            lift_refinement
              ~map:(P.map_root (fun n -> SM.find n arg_names))
              ~nu_arg r
            |> miter @@ add_implication [ PRelation (curr_rel, [], None) ]
        | _ -> type_fail ())
      intr_type.RT.arg_types
  in
  match out_patt with
  | PNone -> return ()
  | PVar v ->
      let pre =
        match intr_type.RT.result_type with
        | Int r ->
            lift_refinement
              ~map:(P.map_root (fun n -> SM.find n arg_names))
              ~nu_arg:(P.var v) r
        | _ -> type_fail ()
      in
      apply_identity_flow ~pre curr_rel body_rel
  | PTuple _ -> type_fail ()

let process_call ~e_id out_patt call_expr curr_rel body_rel =
  let%bind st = copy_state in
  if StringMap.mem call_expr.callee st.bif_types then
    process_intrinsic out_patt call_expr
      (StringMap.find call_expr.callee st.bif_types)
      curr_rel body_rel
  else bind_args ~e_id out_patt call_expr curr_rel body_rel

let add_indexing_assertion arr_ap ind_ap relation =
  let array_len = P.len arr_ap in
  let%bind () =
    add_implication [ PRelation (relation, [], None) ]
    @@ NamedRel ("valid-ind", [ Ap ind_ap; Ap array_len ])
  in
  add_implication [ PRelation (relation, [], None) ]
  @@ rel ~ty:ZInt (mk_relation (Ap array_len) ">" (IConst 0))

let nonnull_flow p = NullConst (P.to_null p, is_nonnull_flag)
(** [apply_patt ~e_id tyenv patt rhs]:

  {[let patt = rhs in ...]}

  Process flow from paths reachable from [rhs] into those from [patt] *)
let apply_patt ~e_id tyenv patt rhs :
    relation -> relation -> ctxt -> ctxt * unit =
  match (patt, rhs) with
  | _, Call c -> process_call ~e_id patt c
  | PNone, _ -> apply_identity_flow ?pre:None
  | _, Var s ->
      let path = P.var s in
      apply_copies ~havoc:false ~sl:(OI.SBind e_id)
      (* 3. Update [ctxt] base on [copy_spec] and havoc state *)
      @@ compute_patt_copies path patt (* 2. Convert to [copy_spec] *)
      @@ path_simple_type tyenv path (* 1. Find [fltype] *)
  | PVar s, Const n -> add_relation_flow [ Const (P.var s, n) ] (* [s = n] *)
  | PVar s, Mkref RNone ->
      add_relation_flow [ Havoc (vderef s); nonnull_flow @@ P.var s ]
  | PVar s, Mkref (RInt n) ->
      add_relation_flow [ Const (vderef s, n); nonnull_flow @@ P.var s ]
  | PVar s, Mkref (RVar v) ->
      apply_copies
        ~flows:[ nonnull_flow @@ P.var s ]
        ~havoc:false ~sl:(OI.SBind e_id)
      @@ compute_copies (P.var v) (vderef s)
      @@ path_simple_type tyenv (P.var v)
  | _, Deref v ->
      let copies =
        compute_patt_copies (vderef v) patt @@ path_simple_type tyenv (vderef v)
      in
      fun ir orel ->
        add_null_check ir (P.var v)
        >> apply_copies
             ~pre:
               [
                 rel ~ty:ZBool
                 @@ mk_relation
                      (Ap (P.to_null @@ P.var v))
                      "=" (BConst is_nonnull_flag);
               ]
             ~havoc:false ~sl:(OI.SBind e_id) copies ir orel
  | PVar t, Tuple tl ->
      let tup_root = P.var t in
      let flows, copies =
        fold_lefti
          (fun i (flows, copies) r ->
            let tgt_ap = P.t_ind tup_root i in
            match r with
            | RNone -> (Havoc tgt_ap :: flows, copies)
            | RInt n -> (Const (tgt_ap, n) :: flows, copies)
            | RVar v ->
                let src_type = path_simple_type tyenv @@ P.var v in
                (flows, ccat (compute_copies (P.var v) tgt_ap src_type) copies))
          ([], empty_copy) tl
      in
      apply_copies ~havoc:false ~sl:(OI.SBind e_id) ~flows copies
  | PTuple _, Tuple _ -> assert false
  | PTuple _, _ -> assert false
  | PVar v, Nondet None -> add_relation_flow [ Havoc (P.var v) ]
  | PVar v, Nondet (Some r) ->
      let refinement = lift_refinement ~nu_arg:(P.var v) r in
      apply_identity_flow ~pre:refinement
  | PVar v, MkArray len_var ->
      fun in_rel out_rel ->
        let%bind () = add_assert (Ap (P.var len_var)) ">=" (IConst 0) in_rel in
        let array_root = P.var v in
        let l = P.var len_var in
        let ind = P.ind array_root in
        let elem = P.elem array_root in
        let valid_sym_ind = [ NamedRel ("valid-ind", [ Ap ind; Ap l ]) ] in
        add_relation_flow ~pre:valid_sym_ind
          [ Const (elem, 0); Copy (l, P.len array_root) ]
          in_rel out_rel
  | PVar v, LengthOf arr ->
      add_relation_flow ?pre:None [ Copy (P.len (P.var arr), P.var v) ]
  | PVar v, Read (arr, ind) ->
      fun in_rel out_rel ->
        let arr_ap = P.var arr in
        let ind_ap = P.var ind in

        let array_ind = P.ind arr_ap in
        let elem_ap = P.elem arr_ap in
        let%bind () = add_indexing_assertion arr_ap ind_ap in_rel in
        let copy_pre_cond =
          PRelation
            (in_rel, [ (array_ind, Ap ind_ap); (elem_ap, Ap (P.var v)) ], None)
        in
        let identity_cond = PRelation (in_rel, [], None) in
        add_implication [ copy_pre_cond; identity_cond ]
        @@ PRelation (out_rel, [], None)
  | PVar v, Null ->
      fun in_rel out_rel ->
        let%bind null_types = get_bound_type e_id in
        let paths = type_to_paths (P.var v) null_types in
        let flows =
          List.map
            (fun p ->
              if P.is_nullity p then NullConst (p, is_null_flag) else Havoc p)
            paths
        in
        RecRelations.null_for_var ~e_id ~ty:null_types v
        >> H.update_null_havoc ~e_id ~ty:null_types v
        >> add_relation_flow ?pre:None flows in_rel out_rel

(** Generate a fresh relation name:
    Simply generate [<function name>-<e_id>-<expression name>] *)
let relation_name ((e_id, _), expr) ctxt =
  let prefix =
    Printf.sprintf "%s-%d-" (Option.value ~default:"main-fn" ctxt.curr_fun) e_id
  in
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
    | Unit -> "unit"
    | Return _ -> "return"
    | Fail -> "fail"
    | LetNewlock _ -> "letnewlock"
    | LetFork _ -> "letfork"
    | Freelock _ -> "freelock"
    | Acq _ -> "acq"
    | Rel _ -> "rel"
    | Wait _ -> "wait"
  in
  prefix ^ kind

(** Generate a relation with the same arguments as [curr_relation] *)
let fresh_relation_for (curr_relation : relation) (((e_id, _), _) as k) ctxt =
  let rel = relation_name k ctxt in
  let _, args, _ = curr_relation in
  let to_ret : relation = (rel, args, Expr e_id) in
  ({ ctxt with relations = to_ret :: ctxt.relations }, to_ret)

let fresh_alias_relation ~e_id ~name ~args ctxt =
  let to_ret = (name, args, AliasUnfold e_id) in
  ({ ctxt with relations = to_ret :: ctxt.relations }, to_ret)

(** Generate a fresh relation name: [<function name>-<e_id>-<postfix>]  *)
let%lq relation_name_with e_id postfix ctxt =
  Printf.sprintf "%s-%d-%s"
    (Option.value ~default:"main-fn" ctxt.curr_fun)
    e_id postfix

(* Generate a fresh relation and register it in [ctxt] *)
let fresh_relation ~e_id ~args ~postfix ctxt =
  let ctxt, name = relation_name_with e_id postfix ctxt in
  let rel : relation = (name, args, Expr e_id) in
  ({ ctxt with relations = rel :: ctxt.relations }, rel)

(** Add [rel] to the set of PTE relations.
  
    Variable [v] has the type of lock or tid.
    NOTE: If you want to allow creating aliases of locks and thread ids by [let] expressions
          and storing them in tuples, use path names instead of variable names. *)
let%lm add_pte_rel v rel ctxt =
  let _, curr_fun = get_curr_fun ctxt in
  { ctxt with pte_rel = SPM.add (curr_fun, v) rel ctxt.pte_rel }

(* Generate a fresh relation for PTE. *)
let fresh_relation_for_pte ~e_id ~args ~key =
  let%bind rel = fresh_relation ~e_id ~args ~postfix:"pte" in
  add_pte_rel key rel >> return rel

let to_cont k = Some k

(** This creates a relation and type environment which extends
   the current relation and type environment with the result
   of binding a value given by the rhs side value recorded in
   the let binding map to [patt].

   This also produces a list of paths bound by the pattern, and any mu
   binders. This is used for removing any havoc information about these paths
   and the recursive mu relations when these paths fall out of scope.
*)
let fresh_bind_relation e_id (relation, tyenv) patt k ctxt =
  (* Arguments of the current relation [relation] *)
  let _, curr_args, _ = relation in

  (* [fltype] of the right-hand side in [let] expression *)
  let bound_type = IntMap.find e_id ctxt.let_types in

  (* Add each path reachable from [patt] into [tyenv], and
     accumulate those paths in [args] *)
  let rec destruct_loop (tyenv, args, rec_paths) patt ty =
    match (patt, ty) with
    | PVar v, ty ->
        (* Add [v: ty] into [tyenv] *)
        let ty_env = (v, ty) :: tyenv in

        (* List all the paths reachable from [v] *)
        let paths = List.rev @@ type_to_paths (P.var v) ty in
        let rec_paths = RecRelations.get_mu_binders (P.var v) ty @ rec_paths in

        (* Give paths [z3_types] and accumulate them in [args] *)
        let args = List.map (fun p -> (p, path_type p)) paths @ args in
        (ty_env, args, rec_paths)
    | PTuple pl, `Tuple tl ->
        List.fold_left2 destruct_loop (tyenv, args, rec_paths) pl tl
    | PTuple _, _ -> assert false
    | PNone, _ -> (tyenv, args, rec_paths)
  in
  let tyenv', args, mu_paths = destruct_loop (tyenv, [], []) patt bound_type in

  (* Newly created paths by [let] expression *)
  let bound_paths = List.map (fun (p, _) -> p) args |> P.PathSet.of_list in

  (* Extended arguments for the new relation *)
  let new_args = curr_args @ List.rev args in

  let name = relation_name k ctxt in
  let relation = (name, new_args, Expr e_id) in
  ( { ctxt with relations = relation :: ctxt.relations },
    (relation, tyenv', (bound_paths, mu_paths)) )

let%lq get_iso_at e_id ctxt =
  let fold = IntSet.mem e_id ctxt.fold_iso in
  let unfold = IntSet.mem e_id ctxt.unfold_iso in
  assert (fold <> unfold || not fold);
  if fold then `IsoFold else if unfold then `IsoUnfold else `None

(** Return a set of typed paths reachable from each variable in [tyenv]  *)
let tyenv_to_paths tyenv =
  List.fold_left
    (fun acc (v, t) -> List.rev_append (type_to_paths (P.var v) t) acc)
    [] tyenv

(** The two sets of havoced paths among the paths whose ownerships are split at location [sl] *)
let%lq split_paths ~sl paths ctxt =
  let _, split_oracle = split_oracle sl ctxt in
  List.fold_left
    (fun (h_src, h_dst) path ->
      (* It may look strange to give the same two [paths].
         When the type environment is split to create a PTE, 
         each path is duplicated into the two paths whose names are the same [path]. *)
      let h_in, h_out = split_oracle path path in
      let add_havoc h hs = if h = `Havoc then P.PathSet.add path hs else hs in
      (add_havoc h_in h_src, add_havoc h_out h_dst))
    (P.PathSet.empty, P.PathSet.empty)
    paths

(* The set of haved paths among the paths whose ownerships are created at location [ml] *)
let%lq join_paths ~ml paths ctxt =
  let havoc_oracle = havoc_oracle ctxt ml in
  List.fold_left
    (fun havoc_state path ->
      let havoced = havoc_oracle path in
      H.add_havoc path havoced havoc_state)
    H.empty_havoc_state paths

(** Process expression is a monadic function that "returns" a boolean indicating
   whether execution within the current function can proceed after executing e.
   This is false iff e must return along all paths. The continuation indicates
   what the "post state" of executing e should flow into; this is the intraprocedural
   successor of e. The relation giving function outputs (which occurs at explicitly
   labelled return statements) is described by the output argument.
*)
let rec process_expr ~output (((relation : relation), tyenv) as st) continuation
    ((e_id, _), e) =
  (* execute two branches, and then bring their results into sync. analyzes branch 1, b2 analyzes branch 2 *)
  let scoped_effect ~b1 ~b2 ctxt =
    (* some trickery here; we abuse the context to record information about the current
       thread of execution (what paths are havoced, etc.) and to accumulate the
       results of the entire analysis. Usually execution is straightline so this
       is actually fine, but at least at conditionals we need to "roll back" the
       current execution state, namely the recursive relations and havoc sets *)
    let orig_recursive_rel = ctxt.recursive_rel in
    let orig_havoc_set = ctxt.havoc_set in
    let ctxt1, r1 = b1 ctxt in
    let roll_back =
      {
        ctxt1 with
        havoc_set = orig_havoc_set;
        recursive_rel = orig_recursive_rel;
      }
    in
    let ctxt2, r2 = b2 roll_back in
    if r1 && r2 then
      let ctxt, recursive_rel =
        P.PathMap.fold
          (fun path bind1 (ctxt, new_map) ->
            let bind2 = P.PathMap.find_opt path ctxt2.recursive_rel in
            let () = assert (bind2 <> None) in
            let bind2 = Option.get bind2 in
            if bind1 = bind2 then (ctxt, P.PathMap.add path bind1 new_map)
            else
              (* if a mu binder is bound to two different relations R and P, compute the join,
                 by effectively unioning the relations

                 (accomplished with a fresh relation U and doing R => U and also P => U)
              *)
              let _, args, _ = bind1 in
              let name = Printf.sprintf !"join-%d-%{P}-%s" e_id path "mu" in
              let rel = (name, args, ExprMu (e_id, path, `Join)) in
              let ctxt =
                {
                  ctxt with
                  impl =
                    [
                      ( [ PRelation (bind1, [], None) ],
                        PRelation (rel, [], None) );
                      ( [ PRelation (bind2, [], None) ],
                        PRelation (rel, [], None) );
                    ]
                    @ ctxt.impl;
                  relations = rel :: ctxt.relations;
                }
              in
              (ctxt, P.PathMap.add path rel new_map))
          ctxt1.recursive_rel (ctxt2, P.PathMap.empty)
      in
      ( {
          ctxt with
          recursive_rel;
          havoc_set = P.PathSet.union ctxt1.havoc_set ctxt2.havoc_set;
        },
        r1 )
    else if r1 then
      ( {
          ctxt2 with
          havoc_set = ctxt1.havoc_set;
          recursive_rel = ctxt1.recursive_rel;
        },
        r1 )
    else (ctxt2, r2)
  in
  (* call back to massage the context that flows out of a let binding, removing the
     bound by the binder from data structures that track information about those
     paths (havoc and mu relations). *)
  let post_bind (paths, mu_binders) f ctxt =
    let pset = P.PathSet.of_list mu_binders in
    let ctxt, r = f ctxt in
    ( {
        ctxt with
        havoc_set = P.PathSet.diff ctxt.havoc_set paths;
        recursive_rel =
          P.PathMap.filter
            (fun p _ -> not @@ P.PathSet.mem p pset)
            ctxt.recursive_rel;
      },
      r )
  in
  let%lm save_snapshot ctxt =
    {
      ctxt with
      snapshots =
        IntMap.add e_id
          { gamma = tyenv; relation; mu_relations = ctxt.recursive_rel }
          ctxt.snapshots;
    }
  in
  let%bind iso = get_iso_at e_id in
  save_snapshot
  >>
  match e with
  | Unit -> (
      match continuation with
      | Some out_relation ->
          (* intra procedural successor *)
          apply_identity_flow relation out_relation >> return true
      (* should only happen at the main function *)
      | None -> return false)
  | Return v ->
      let () = assert (output <> None) in
      let out_relation, ret_var, out_rec_rel = Option.get output in
      (* luckily the deep unpleasantness of copies is completely abstracted away by compute
         copies and apply copies. NB the use of out_rec_rel which says
         what recursive relations should be the "flow targets" of the return/output relations *)
      let copies =
        compute_copies (P.var v) ret_var @@ path_simple_type tyenv (P.var v)
      in
      apply_copies ~out_rec_rel ~havoc:false ~sl:(SRet e_id) copies relation
        out_relation
      >> return false
  | Fail -> add_assert (IConst 0) "=" (IConst 1) relation >> return false
  | Seq (e1, e2) ->
      let%bind e2_rel = fresh_relation_for relation e2 in
      let%bind flg = process_expr ~output st (to_cont e2_rel) e1 in
      (* otherwise we have dead code *)
      assert flg;
      process_expr (e2_rel, tyenv) ~output continuation e2
  | Assign (lhs, IInt i, k) ->
      let%bind k_rel = fresh_relation_for relation k in
      add_null_check relation (P.var lhs)
      >> const_assign (P.deref @@ P.var lhs) i relation k_rel
      >> process_expr ~output (k_rel, tyenv) continuation k
  | Assign (lhs, IVar rhs, k) when iso = `IsoFold ->
      let%bind k_rel = fresh_relation_for relation k in
      let out_ap = P.var lhs in
      let ty = path_simple_type tyenv out_ap in
      add_null_check relation (P.var lhs)
      >> do_fold_copy ~e_id rhs lhs ty relation k_rel
      >> process_expr ~output (k_rel, tyenv) continuation k
  | Assign (lhs, IVar rhs, k) ->
      let%bind k_rel = fresh_relation_for relation k in
      let copies =
        compute_copies (P.var rhs) (vderef lhs) @@ List.assoc rhs tyenv
      in
      add_null_check relation (P.var lhs)
      >> apply_copies ~havoc:true ~sl:(SBind e_id) copies relation k_rel
      >> process_expr ~output (k_rel, tyenv) continuation k
  | Update (arr, ind, rhs, k) ->
      (* We model array updates by creating two implications to the successor state. The
         first considers the case where the symbolic index variable is not equal to the
         concrete index. In this case, the value of the array element is as in the input
         relation, i.e., before this update. In the second implication the symbolic
         index is constrained to be equal to the actual index to the operation, and
         the corresponding array element is constrained to be equal to the rhs argument. *)
      let%bind k_rel = fresh_relation_for relation k in
      let array_ap = P.var arr in
      let ind_ap = P.var ind in
      let rhs_ap = P.var rhs in

      let sym_ind = P.ind array_ap in
      let sym_elem = P.elem array_ap in
      [%m
        (* asserts that the index is within bounds and the length is greater than 0 *)
        add_indexing_assertion array_ap ind_ap relation;
        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation
             (k_rel, [ (sym_elem, Ap rhs_ap); (sym_ind, Ap ind_ap) ], None);
        add_implication
          [
            PRelation (relation, [], None);
            rel ~ty:ZInt @@ mk_relation (Ap sym_ind) "!=" (Ap ind_ap);
          ]
        @@ PRelation (k_rel, [], None);
        process_expr ~output (k_rel, tyenv) continuation k]
  | Cond (v, e1, e2) ->
      let%bind e1_rel = fresh_relation_for relation e1 in
      let%bind e2_rel = fresh_relation_for relation e2 in

      let mk_pre rel_cond =
        Relation
          (RT.{ rel_op1 = Ap (P.var v); rel_cond; rel_op2 = IConst 0 }, ZInt)
      in
      [%m
        apply_identity_flow ~pre:[ mk_pre "=" ] relation e1_rel;
        apply_identity_flow ~pre:[ mk_pre "!=" ] relation e2_rel;
        scoped_effect
          ~b1:(process_expr ~output (e1_rel, tyenv) continuation e1)
          ~b2:(process_expr ~output (e2_rel, tyenv) continuation e2)]
  | NCond (v, e1, e2) ->
      let%bind e1_rel = fresh_relation_for relation e1 in
      let%bind e2_rel = fresh_relation_for relation e2 in
      let mk_pre null =
        let null_ap = Ap (P.to_null @@ P.var v) in
        Relation
          ( RT.{ rel_op1 = null_ap; rel_cond = "="; rel_op2 = BConst null },
            ZBool )
      in
      let var_type = path_simple_type tyenv @@ P.var v in
      [%m
        apply_identity_flow ~pre:[ mk_pre is_null_flag ] relation e1_rel;
        apply_identity_flow ~pre:[ mk_pre is_nonnull_flag ] relation e2_rel;
        scoped_effect
          ~b1:
            ((* creates arbitrary relations for every mu binder under the (provably null) variable *)
             RecRelations.null_for_var ~e_id ~ty:var_type v
            >> (* use the havoc state determined by the magic map *)
            H.update_null_havoc ~e_id ~ty:var_type v
            >> process_expr ~output (e1_rel, tyenv) continuation e1)
          ~b2:(process_expr ~output (e2_rel, tyenv) continuation e2)]
  | Let (PVar lhs, Mkref (RVar rhs), k) when iso = `IsoFold ->
      let%bind k_rel, tyenv', bind_info =
        fresh_bind_relation e_id st (PVar lhs) k
      in
      let%bind bound_ty = get_bound_type e_id in
      do_fold_copy ~e_id rhs lhs bound_ty relation k_rel
      >> post_bind bind_info
         @@ process_expr ~output (k_rel, tyenv') continuation k
  | Let (p, Deref rhs, k) when iso = `IsoUnfold ->
      let ref_ty = path_simple_type tyenv @@ P.var rhs in
      let%bind k_rel, tyenv', bind_info = fresh_bind_relation e_id st p k in
      let%bind unfolded_type = get_bound_type e_id in
      (* Rather than have unfold_to reason about patterns and so on, we generate
         the unfolding to a dummy variable $uf, and the compute the assignments
         from dummy variable $uf to the pattern given in the LHS.

         This latter assingment is used for the out_mapping argument.
      *)
      let copies = compute_patt_copies (P.var "$uf") p unfolded_type in
      let out_mapping =
        List.fold_left
          (fun acc (uf, real_path, _) -> PPMap.add uf real_path acc)
          PPMap.empty
        @@ to_copy_stream copies
      in
      let out_mapping =
        List.fold_left
          (fun acc (_, uf, real_path, _) -> PPMap.add uf real_path acc)
          out_mapping
        @@ to_mu_copies copies
      in
      add_null_check relation (P.var rhs)
      >> do_unfold_copy ~with_havoc:true ~e_id ~out_mapping rhs "$uf" ref_ty
           relation k_rel
      >> post_bind bind_info
         @@ process_expr ~output (k_rel, tyenv') continuation k
  | Let (patt, rhs, k) ->
      let%bind k_rel, tyenv', bind_info = fresh_bind_relation e_id st patt k in
      apply_patt ~e_id tyenv patt rhs relation k_rel
      >> post_bind bind_info
         @@ process_expr ~output (k_rel, tyenv') continuation k
  | Assert (assrt, k) ->
      let%bind k_rel = fresh_relation_for relation k in
      add_assert_cond assrt relation
      >> apply_identity_flow relation k_rel
      >> process_expr ~output (k_rel, tyenv) continuation k
  | Alias (lhs, rhs, k) when iso = `IsoUnfold ->
      (* This means that the root of a recursive type
         aliases with the mu binder under another recursive type.
         Our basic strategy is as follows:
         + unfold the type containing the target mu binder to a temporary relation.
         Thus, the "target" of the alias has a similar shape to the "source" type.
         + Immediately fold the unfolded relation back up. However, when folding back up,
         we use the copy policy and rec_ext facilities of fold to to ensure that paths
         in the (now unfolded mu) and the those in the "source" unfolded type are shared,
         ensuring the values in the result of the fold reflects any information from the
         unfolded type being aliased in.
      *)
      let rec has_mu_binder : fltype -> bool = function
        | `Int | `TVar | `IntArray | `Ref _ -> false
        | `Mu _ -> true
        | `Tuple tl -> List.exists has_mu_binder tl
        | `Lock _ | `ThreadID _ -> false
      in
      (* TODO: add null ante pre *)
      (* If we have an isounfold here, then one of the alias
         paths must go to a mu binder. This finds
         the root of the recursive type being unfolded.


         TODO: (This is an extremely brittle way for this to work, we should
         do better)

         If the result is found, this returns the the type under the root
         of the recursive type, the (reversed) list of steps followed to reach the root,
         and the remaining steps to reach the mu binder
      *)
      let rec find_unfold_point rev t rem =
        match (t, rem) with
        | `Deref :: r, `Ref (_, t) ->
            if has_mu_binder t then Some (t, r, rev)
            else find_unfold_point (`Deref :: rev) r t
        | `Proj i :: r, `Tuple tl ->
            find_unfold_point (`Proj i :: rev) r (List.nth tl i)
        | [], _ -> None
        | _, _ -> assert false
      in
      (* if this path goes to a mu, return the type
         under root of the containing recursive type,
         the path to the root, and the path to the mu,
         expressed relative to the path tot he root.

         Otherwise, simply returns the path


         (This is either or is represented with the result type,
         which uses the unfortunately named constructors Ok Error,
         but really we are (ab)using it to represent one of two possible results
         that has very nice interoperation with the Option module)
      *)
      let prepare_alias path =
        let root, steps, suff =
          (path : P.concr_ap :> P.root * P.steps list * P.suff)
        in
        let v =
          match (root, suff) with P.Var v, `None -> v | _ -> assert false
        in
        let ty = List.assoc v tyenv in
        find_unfold_point [] (List.rev steps) ty
        |> Option.map (fun (t, to_mu, ctxt) ->
               let p = P.var v in
               let p = List.fold_left P.extend p @@ List.rev ctxt in
               let to_mu = List.fold_left P.extend P.template to_mu in
               (t, to_mu, p, path))
        |> Option.to_result ~none:path
      in
      let lp = prepare_alias lhs in
      let rp = prepare_alias rhs in

      (* + ref_cont is the type under the root of the mu
         + mu_path is the path to the mu binder, relative to path_to_ref
         + path_to_ref is the path to the root of the containing recursive type
         + full_path is the full path to the mu binder
         + unfolded path is the path to the value to be folded by this alias
      *)
      let ref_cont, mu_path, path_to_ref, full_path, unfolded_path =
        match (lp, rp) with
        | Error unfolded_path, Ok (ref_cont, mu_path, path_to_ref, full_path)
        | Ok (ref_cont, mu_path, path_to_ref, full_path), Error unfolded_path ->
            (ref_cont, mu_path, path_to_ref, full_path, unfolded_path)
        | _, _ -> assert false
      in
      let%bind k_rel = fresh_relation_for relation k in

      (* TODO: rename lhs_type to uf_type *)
      (* This is the type we expect to find at path_to_ref (as expressed below) *)
      let lhs_type = path_simple_type tyenv unfolded_path in

      assert (match lhs_type with `Ref (_, t') -> t' = ref_cont | _ -> false);
      (* In order to make the mu binders match, we need to unfold the target type, i.e.
         the aliased type. Recall this is to make the target of aliasing match the shape
         of the unfolded source.
      *)
      let aliased_type = deep_type_normalization ref_cont in
      (* the unfolding is down to a dummy $uf variable *)
      let temp_args =
        type_to_paths (P.var "$uf") aliased_type
        |> List.map (fun p -> (p, path_type p))
      in
      let curr_rel, curr_args, _ = relation in
      let%bind temp_rel =
        fresh_alias_relation ~e_id ~name:(curr_rel ^ "$alias")
          ~args:(curr_args @ temp_args)
      in
      let%lm alias_unfold p1 p2 ty in_rel out_rel ctxt =
        RecursiveRefinements.unfold_to ~e_id ~with_havoc:false
          ~out_mapping:PPMap.id_map ty p1 p2 in_rel out_rel ctxt
      in
      (* unfold *)
      let%bind () =
        alias_unfold path_to_ref (P.var "$uf") lhs_type relation temp_rel
      in
      (* the path to the (now unfolded) mu in $uf *)
      let flow_root = P.root_at ~child:mu_path ~parent:(P.var "$uf") in
      let folded_target = full_path in
      (* the aliasing can be viewed as a "copy" from the source (found at unfolded path)
         and the (now unfolded) [flow_root] *)
      let copies = compute_copies unfolded_path flow_root lhs_type in
      let copy_stream = to_copy_stream copies in
      (* Which copies are occurring under a mu, and which not? *)
      let direct_copies, weak_copies =
        copy_stream |> List.partition (fun (_, _, k) -> k = `Direct)
      in

      (* To copy information from the unfolded version while simultaneously copying
         information from the source recursive type, we use the following trick:

         In the following, let x and y be the path of a location at the same
         relative location under the mu binder in question, and let
         b and c be a concrete location. The resulting
         implication is generated as:

         R(b, y!pass, c, y!pass) /\ R(b, x, b, x) => Q(b, x, b, y!pass)

         So we make sure that any relationship satsified by y is satisfied by x and vice versa,
         without constraining them to be equal. However, we do b and c to be equal (as the copy
         is direct).
      *)

      (* generate the y -> y!pass substitution *)
      let pass_through_subst =
        List.map (fun (s, _, _) -> (s, to_pass_ap s)) weak_copies
      in
      (* this rename is applied to a second copy of the input relation for weak copies.
         We apply the y->y!pass and x -> y!pass substitution

         XXX: uhhhh, wanna apply the direct copies to...?
      *)
      let rename_weak =
        pass_through_subst
        @ List.map (fun (s, d, _) -> (d, to_pass_ap s)) weak_copies
      in
      (* rename y->y!pass and c -> b *)
      let rename_out =
        pass_through_subst @ List.map (fun (s, d, _) -> (s, d)) direct_copies
      in
      (* rename y -> x and c -> b, this is applied to a different copy of the input relation *)
      let rename_src = List.map (fun (s, d, _) -> (s, d)) copy_stream in

      let%lm do_alias_fold ctxt =
        let dst_oracle p =
          (* when we fold uf back into the original type, it we will query for the havoc
             state of some paths that are not actually touched by the alias (i.e., the havoc
             state of the head elements in the type containing the target mu. In
             that case, just call back on the current havoc state *)
          if
            P.has_prefix ~prefix:folded_target p && p <> P.to_null folded_target
          then havoc_oracle ctxt (OI.MAlias e_id) p
          else P.PathSet.mem p ctxt.havoc_set
        in
        (* the uf state is going to be dropped anyway *)
        let src_oracle _ = true in
        let havoc_oracle = havoc_oracle ctxt (OI.MAlias e_id) in
        (* the havoc of the "source", already unfolded type. (called "var" because the
           language grammar used to require this be rooted at a plain variable) *)
        let var_havoc =
          copy_stream
          |> List.fold_left
               (fun acc (src, _, k) ->
                 let havoc = havoc_oracle src in
                 let acc = H.add_havoc src havoc acc in
                 match k with
                 | `Mu (under_mu_path, binder, _, ty) ->
                     H.add_mu_havoc ~binder ~ty under_mu_path havoc acc
                 | _ -> acc)
               H.empty_havoc_state
        in
        let by_havoc = H.to_rec_havoc var_havoc in
        (* walk the source type, and generate the new, joined recursive refinements from
           combinining information from the unfolded temp type. In addition, this records
           the relations to conjoin in fold_to using the rec_ext functionality
        *)
        let ante, ctxt =
          to_mu_copies copies
          |> List.fold_left
               (fun (ante, ctxt) (_, src_root, dst_root, ty) ->
                 let src_rel = P.PathMap.find src_root ctxt.recursive_rel in
                 let ante =
                   P.PathMap.add dst_root (PRelation (src_rel, [], None)) ante
                 in
                 let dst_rel = P.PathMap.find dst_root ctxt.recursive_rel in
                 let ctxt =
                   RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id
                     ~ante:
                       [
                         PRelation (src_rel, [], None);
                         PRelation (dst_rel, [], None);
                       ]
                     src_root ty ctxt
                 in
                 (ante, ctxt))
               (P.PathMap.empty, ctxt)
        in
        (* compute the head substitution for when generating the mu relation that incorporates
           the head and tails of the temp unfolded type, it should also include the
           corresponding head and tails of the "source" *)
        let hd_subst =
          parallel_type_walk P.template unfolded_path lhs_type
            (fun _ _ () -> `Cont ())
            (fun () i o acc -> (o, Ap i) :: acc)
            () []
        in

        let havoc_ext ~havoc ~stable =
          ( P.PathSet.union havoc var_havoc.havoc,
            P.PathSet.union stable var_havoc.stable )
        in
        (* the extensions are only valid for the mu binder targeted by the alias expression *)
        let rec_ext =
          P.PathMap.singleton
            (P.root_at ~child:mu_path ~parent:(P.deref P.template))
            (hd_subst, ante)
        in
        let open RecursiveRefinements in
        (* easy! *)
        let ctxt =
          fold_to ~oracle:(dst_oracle, src_oracle) ~e_id
            ~copy_policy:(Custom { rename_src; rename_out; rename_weak })
            ~rec_ext ~havoc_ext lhs_type (P.var "$uf") path_to_ref temp_rel
            k_rel ctxt
        in
        (* now remove all of the $uf stuff *)
        let uf_root = P.var "$uf" in
        let concr_root_p = Fun.negate @@ P.has_prefix ~prefix:uf_root in
        let havoc_set = P.PathSet.filter concr_root_p ctxt.havoc_set in
        {
          ctxt with
          havoc_set;
          recursive_rel =
            P.PathMap.filter (fun p _ -> concr_root_p p) ctxt.recursive_rel;
        }
      in
      do_alias_fold >> process_expr ~output (k_rel, tyenv) continuation k
  | Alias (lhs_path, rhs_ap, k) ->
      let null_ante_paths ap =
        let rec null_ante_paths acc ap =
          match P.tail ap with
          | None -> acc
          | Some e ->
              let p = P.parent ap in
              if e = `Deref then null_ante_paths (P.to_null p :: acc) p
              else null_ante_paths acc p
        in
        null_ante_paths [] ap
      in
      let%bind k_rel = fresh_relation_for relation k in
      let lhs_type = path_simple_type tyenv lhs_path in
      let rhs_subst = compute_copies lhs_path rhs_ap lhs_type in
      let%bind havoc_oracle = gen_for_alias e_id in
      (* The basic idea (which is reflected in the above)
         is to model aliasing by introducing a constraint that all values reachable
         from the operand paths must be equal (because they alias). As a consequence, Z3
         must conclude that the invariants that hold on the two locations must incorporate
         information from inputs.

         left/right are used for weak copies of, you guessed it, weak locations. If
         any weak locations are involed, then we use two copies of the input
         relation in the antecedent, with the argument substitution
         R(x, x) /\ R(y, y) => Q(x, y) (where x and y are two summary locations).
      *)
      let direct, left, right, hstate =
        List.fold_left
          (fun (direct, left, right, hstate) (src, dst, k) ->
            let hstate =
              if P.to_null lhs_path = src then hstate
              else
                let s_havoc = havoc_oracle src in
                let d_havoc = havoc_oracle dst in
                let hstate =
                  H.add_havoc src s_havoc hstate |> H.add_havoc dst d_havoc
                in
                match k with
                | `Mu (under_mu_path, src_root, dst_root, ty) ->
                    H.add_mu_havoc ~binder:src_root ~ty under_mu_path s_havoc
                      hstate
                    |> H.add_mu_havoc ~binder:dst_root ~ty under_mu_path d_havoc
                | _ -> hstate
            in
            match k with
            | `Direct -> ((src, dst) :: direct, left, right, hstate)
            | `Mu _ -> (direct, (src, dst) :: left, (dst, src) :: right, hstate))
          ([], [], [], H.empty_havoc_state)
        @@ to_copy_stream rhs_subst
      in
      let direct = List.map lift_copy direct in
      let ante =
        if left <> [] then
          let () = assert (right <> []) in
          [
            PRelation (relation, direct @ List.map lift_copy right, None);
            PRelation (relation, direct @ List.map lift_copy left, None);
          ]
        else [ PRelation (relation, direct, None) ]
      in
      (* for the aliasing to succeed, all references traversed must be non-null *)
      let extend_nonnull nfs l =
        List.fold_left
          (fun acc nf -> NullCons (Ap nf, BConst is_nonnull_flag) :: acc)
          l nfs
      in
      let must_inhabit_paths =
        null_ante_paths lhs_path @ null_ante_paths rhs_ap
      in
      let ante = extend_nonnull must_inhabit_paths ante in
      let%bind havoc_set = get_havoc_state in
      let havoc_set =
        P.PathSet.union hstate.havoc @@ P.PathSet.diff havoc_set hstate.stable
      in
      let out_subst = augment_havocs direct havoc_set in
      let%lm alias_recursive ctxt =
        let by_havoc = H.to_rec_havoc hstate in
        (* conjoin the recursive refinements, in the same way as in the
           above alias case. In this case, we use the same antecedent (a conjoining
           of the two mu relations) but generate two relations due
           to differences in havocing.
        *)
        to_mu_copies rhs_subst
        |> List.fold_left
             (fun ctxt (_, src, dst, ty) ->
               let src_rel = P.PathMap.find src ctxt.recursive_rel in
               let dst_rel = P.PathMap.find dst ctxt.recursive_rel in
               let ante =
                 [
                   PRelation (src_rel, [], None); PRelation (dst_rel, [], None);
                 ]
               in
               RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante src
                 ty ctxt
               |> RecRelations.recursive_rel_with_havoc ~by_havoc ~e_id ~ante
                    dst ty)
             ctxt
      in
      List.fold_left
        (fun seq p -> seq >> add_null_path_check relation p)
        (return ()) must_inhabit_paths
      >> set_havoc_state ~rel:(get_relation_ident k_rel) havoc_set
      >> alias_recursive
      >> add_implication ante @@ PRelation (k_rel, out_subst, None)
      >> process_expr ~output (k_rel, tyenv) continuation k
  | LetNewlock (v, k) ->
      (* Generate a fresh relation [k_rel] and add a lock [v] into [tyenv'] *)
      let%bind k_rel, tyenv', bind_info =
        fresh_bind_relation e_id st (PVar v) k
      in

      (* [bind_info] is the set of paths reachable from a lock [v]: empty set *)
      assert (bind_info = (P.PathSet.empty, []));

      (* paths reachable from variables in [tyenv'] *)
      let paths = tyenv_to_paths tyenv' in

      (* Relation for the PTE of lock [v] *)
      let%bind pte_relation =
        fresh_relation_for_pte ~e_id ~args:(type_paths paths) ~key:v
      in

      (* Havoced paths when the type environment is split and the PTE is created. *)
      let%bind havoc_set_thread, havoc_set_pte =
        split_paths ~sl:(SBind e_id) paths
      in

      (* print_endline @@ P.PathSet.to_string havoc_set_pte; *)
      [%m
        add_havoc_state ~rel:(get_relation_ident k_rel) havoc_set_thread;
        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation (k_rel, havoc_set_to_subst havoc_set_thread, None);
        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation (pte_relation, havoc_set_to_subst havoc_set_pte, None);
        process_expr ~output (k_rel, tyenv') continuation k]
  | LetFork (v, e, k) ->
      (* Generate a fresh relation [k_rel] and add a lock [v] into [tyenv'] *)
      let%bind k_rel, tyenv', bind_info =
        fresh_bind_relation e_id st (PVar v) k
      in

      (* [bind_info] is the set of paths reachable from a lock [v]: empty set *)
      assert (bind_info = (P.PathSet.empty, []));

      (* paths reachable from variables in the current environment *)
      let paths = tyenv_to_paths tyenv' in

      let _, args, _ = relation in

      (* Pre-relation of the child thread *)
      let%bind thread_pre_relation =
        fresh_relation ~e_id ~args ~postfix:"thread-pre"
      in

      (* Post-relation of the child thread *)
      (* child thread 終了時の関係(ただし，PTE から到達可能なパスのみについて)  *)
      let%bind thread_post_relation =
        fresh_relation ~e_id ~args ~postfix:"thread-post"
      in
      add_pte_rel v thread_post_relation
      >>
      (* The current havoc set *)
      let%bind havoc_set = get_havoc_state in

      (* havoc sets of the child thread and the parent one *)
      let%bind havoc_set_child, havoc_set_parent =
        split_paths ~sl:(SBind e_id) paths
      in

      (* Process the child thread *)
      add_havoc_state
        ~rel:(get_relation_ident thread_pre_relation)
        havoc_set_child
      >>
      let%bind _flg =
        process_expr ~output:None
          (thread_pre_relation, tyenv)
          (Some thread_post_relation) e
      in

      [%m
        (* roll back *)
        set_havoc_state ~rel:(get_relation_ident k_rel)
        @@ P.PathSet.union havoc_set havoc_set_parent;

        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation
             (thread_pre_relation, havoc_set_to_subst havoc_set_child, None);
        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation (k_rel, havoc_set_to_subst havoc_set_parent, None);
        process_expr ~output (k_rel, tyenv') continuation k]
  | Freelock (v, k) | Acq (v, k) | Wait (v, k) ->
      (* Generate a fresh relation [k_rel] *)
      let%bind k_rel = fresh_relation_for relation k in

      let paths = tyenv_to_paths tyenv in
      let%bind hstate = join_paths ~ml:(MGen e_id) paths in
      let%bind havoc_set = get_havoc_state in
      let havoc_set =
        P.PathSet.union hstate.H.havoc
        @@ P.PathSet.diff havoc_set hstate.H.stable
      in

      let%bind pte_rel = get_pte_relation v in
      [%m
        set_havoc_state ~rel:(get_relation_ident k_rel) havoc_set;
        apply_identity_flow
          ~pre:[ PRelation (pte_rel, [], None) ]
          relation k_rel;
        process_expr ~output (k_rel, tyenv) continuation k]
  | Rel (v, k) ->
      (* Generate a fresh relaton [k_rel] *)
      let%bind k_rel = fresh_relation_for relation k in

      let paths = tyenv_to_paths tyenv in

      (* [_havoc_set_pte] is the set of paths which root variables are not included in the PTE. *)
      let%bind havoc_set, _havoc_set_pte = split_paths ~sl:(SBind e_id) paths in

      let%bind pte_rel = get_pte_relation v in
      [%m
        add_havoc_state ~rel:(get_relation_ident k_rel) havoc_set;
        add_implication [ PRelation (relation, [], None) ]
        @@ PRelation (k_rel, havoc_set_to_subst havoc_set, None);
        apply_identity_flow relation pte_rel;
        process_expr ~output (k_rel, tyenv) continuation k]

let analyze_function fn ctxt =
  let {
    in_rel = in_nm, in_args, isrc;
    out_rel = out_nm, out_args, osrc;
    f_type = fn_type;
    in_recursive_rel;
    out_recursive_rel;
  } =
    StringMap.find fn.name ctxt.fenv
  in
  let initial_env = List.map2 (fun v ty -> (v, ty)) fn.args fn_type.arg_types in
  let arg_mapping =
    fold_lefti
      (fun i acc nm -> StringMap.add (P.arg_name i) nm acc)
      StringMap.empty fn.args
  in
  let map_arg_root = Paths.map_root (fun t -> StringMap.find t arg_mapping) in
  let map_args =
    List.map (fun (p, ty) ->
        let p' = map_arg_root p in
        (p', ty))
  in

  (* The initial havoc set as determined by the ownership operation *)
  let havoc_set =
    fold_left2i
      (fun i acc nm ty ->
        List.fold_left
          (fun acc path ->
            let arg_id = P.map_root (fun _ -> P.arg_name i) path in
            if havoc_oracle ctxt (OI.MArg fn.name) arg_id then
              P.PathSet.add path acc
            else acc)
          acc
        @@ type_to_paths (P.var nm) ty)
      P.PathSet.empty fn.args fn_type.arg_types
  in
  let start_rel, direct_out =
    fold_lefti
      (fun i acc (arg_name, ty) ->
        let mu_binders = RecRelations.get_mu_binders P.template ty in
        let formal_name = P.arg i in
        List.fold_left
          (fun (start_rel, out_list) mu_loc ->
            let formal_root = P.root_at ~child:mu_loc ~parent:formal_name in
            let arg_root = P.root_at ~child:mu_loc ~parent:(P.var arg_name) in
            let orel = P.PathMap.find formal_root out_recursive_rel in
            let irel = P.PathMap.find formal_root in_recursive_rel in
            (P.PathMap.add arg_root irel start_rel, (arg_root, orel) :: out_list))
          acc mu_binders)
      (P.PathMap.empty, []) initial_env
  in
  let direct_flow =
    P.PathMap.filter (fun p _ -> P.has_prefix ~prefix:P.ret p) out_recursive_rel
  in
  let mapped_in_args = map_args in_args in
  let mapped_out_args = map_args out_args in
  let cont =
    Some ((out_nm, mapped_out_args, osrc), P.ret, (direct_flow, direct_out))
  in
  let add_omit nm ctxt =
    StringMap.find_opt nm ctxt.omit_set
    |> Option.fold ~none:ctxt ~some:(fun set ->
           let set' = P.PathSet.map map_arg_root set |> P.PathSet.union set in
           { ctxt with omit_set = StringMap.add nm set' ctxt.omit_set })
  in
  let ctxt = add_omit in_nm ctxt |> add_omit out_nm in
  let ctxt, _ =
    process_expr
      ((in_nm, mapped_in_args, isrc), initial_env)
      ~output:cont None fn.body
      {
        ctxt with
        curr_fun = Some fn.name;
        havoc_set;
        recursive_rel = start_rel;
      }
  in
  ctxt

let analyze_main start_rel main ctxt =
  let ctxt, _ = process_expr (start_rel, []) ~output:None None main ctxt in
  ctxt

let infer ~opts (simple_theta, side_results) o_hints (fns, main) =
  let lift_and_unfold p = deep_type_normalization @@ simple_to_fltype p in
  let simple_theta =
    StringMap.map
      (fun ft ->
        {
          arg_types = List.map lift_and_unfold ft.arg_types;
          ret_type = lift_and_unfold ft.ret_type;
        })
      simple_theta
  in
  let fenv, relations, omit_set =
    StringMap.fold
      (fun name ty (theta, rel, os) ->
        let arg_paths =
          List.mapi
            (fun i arg_t -> type_to_paths ~pre:true (P.arg i) arg_t)
            ty.arg_types
        in
        let get_havoced_paths ml p ty =
          walk_type ty
            (fun k path ->
              match k with
              | `Ref ->
                  let o = OI.GenMap.find (ml, path) o_hints.OI.gen in
                  if o = 0.0 then
                    `K
                      (fun ty acc ->
                        match ty with
                        | `Ref (_, t) -> type_to_paths (P.deref path) t @ acc
                        | _ -> assert false)
                  else `Cont (P.deref path)
              | `Array ->
                  let o = OI.GenMap.find (ml, path) o_hints.OI.gen in
                  if o = 0.0 then
                    `K (fun _ acc -> P.ind path :: P.elem path :: acc)
                  else `Cont path
              | _ -> `Cont (path_step k path))
            (fun _ acc -> acc)
            p []
        in
        let in_rel_types =
          List.map (fun p -> (p, path_type p)) @@ List.concat arg_paths
        in
        let ret_rel =
          type_to_paths P.ret ty.ret_type
          |> List.map (fun p -> (p, path_type p))
        in
        let out_rel_types = in_rel_types @ ret_rel in
        let in_havoc_paths =
          fold_lefti
            (fun i acc t ->
              get_havoced_paths (OI.MArg name) (P.arg i) t
              |> List.fold_left (fun s p -> P.PathSet.add p s) acc)
            P.PathSet.empty ty.arg_types
        in
        let out_havoc_paths =
          fold_lefti
            (fun i acc t ->
              get_havoced_paths (OI.MOut name) (P.arg i) t
              |> List.fold_left (fun s p -> P.PathSet.add p s) acc)
            P.PathSet.empty ty.arg_types
        in
        let in_rel = (name ^ "-in", in_rel_types, Fun (name, `In)) in
        let out_rel = (name ^ "-out", out_rel_types, Fun (name, `Out)) in
        let () =
          assert (not @@ StringMap.mem (get_relation_ident in_rel) os);
          assert (not @@ StringMap.mem (get_relation_ident out_rel) os)
        in
        let os =
          StringMap.add (get_relation_ident in_rel) in_havoc_paths os
          |> StringMap.add (get_relation_ident out_rel) out_havoc_paths
        in
        let in_rec_rel, out_rec_rel, rel =
          fold_lefti
            (fun i acc arg_t ->
              RecRelations.get_recursive_roots (P.arg i) arg_t
              |> List.fold_left
                   (fun acc (root, ty) ->
                     let args =
                       type_to_paths P.template ty
                       |> List.map (fun p -> (p, path_type p))
                     in
                     RecRelations.get_mu_binders root ty
                     |> List.fold_left
                          (fun (in_rec_rel, out_rec_rel, rel) mu_binder ->
                            let f suff mu =
                              Printf.sprintf !"%s-%s-%{P}-%s" name suff mu "mu"
                            in
                            let in_name = f "in" mu_binder in
                            let out_name = f "out" mu_binder in
                            let in_rel =
                              (in_name, args, FunMu (name, `In, mu_binder))
                            in
                            let out_rel =
                              (out_name, args, FunMu (name, `Out, mu_binder))
                            in
                            ( RecRelations.update_rel_map mu_binder in_rel
                                in_rec_rel,
                              RecRelations.update_rel_map mu_binder out_rel
                                out_rec_rel,
                              in_rel :: out_rel :: rel ))
                          acc)
                   acc)
            (P.PathMap.empty, P.PathMap.empty, rel)
            ty.arg_types
        in
        let out_rec_rel, rel =
          RecRelations.get_recursive_roots P.ret ty.ret_type
          |> List.fold_left
               (fun acc (root, ty) ->
                 let args =
                   type_to_paths P.template ty
                   |> List.map (fun p -> (p, path_type p))
                 in
                 RecRelations.get_mu_binders root ty
                 |> List.fold_left
                      (fun (out_rec_rel, rel) root ->
                        let nm =
                          Printf.sprintf !"%s-out-%{P}-%s" name root "mu"
                        in
                        let ret_rel = (nm, args, FunMu (name, `Out, root)) in
                        ( RecRelations.update_rel_map root ret_rel out_rec_rel,
                          ret_rel :: rel ))
                      acc)
               (out_rec_rel, rel)
        in
        let ftype =
          {
            in_recursive_rel = in_rec_rel;
            out_recursive_rel = out_rec_rel;
            in_rel;
            out_rel;
            f_type = ty;
          }
        in
        (StringMap.add name ftype theta, in_rel :: out_rel :: rel, os))
      simple_theta
      (StringMap.empty, [], StringMap.empty)
  in

  (* Mapping from pairs of function names and variable names to relations.

     For parameters of functions which types have PTEs, generate fresh relations for the PTEs. *)
  let pte_rel =
    List.fold_left
      (fun acc fn ->
        let fn_name = fn.name in
        let params = fn.args in
        let ty = SM.find fn_name simple_theta in
        assert (List.length params = List.length ty.arg_types);

        (* Paths reachable from parameters of function [fn_name] *)
        let args =
          let tyenv = List.combine params ty.arg_types in
          tyenv |> tyenv_to_paths |> type_paths
        in
        List.fold_left2
          (fun acc v t ->
            match t with
            | `Lock _ | `ThreadID _ ->
                let pte_rel : relation =
                  let rel_name = Printf.sprintf "%s-%s-pte" fn_name v in
                  (rel_name, args, PTE (fn_name, v))
                in
                SPM.add (fn_name, v) pte_rel acc
            | _ -> acc)
          acc params ty.arg_types)
      StringPairMap.empty fns
  in

  let relations =
    let pte_relations = snd @@ List.split @@ SPM.bindings pte_rel in
    List.rev_append pte_relations relations
  in

  let start_name = "program-start" in
  let entry_relation = (start_name, [], Start) in
  let relations = entry_relation :: relations in

  let fn_params =
    let open RefinementTypes in
    List.fold_left
      (fun acc { name; args; _ } -> SM.add name args acc)
      SM.empty fns
    |> SM.fold
         (fun name it acc ->
           let args =
             List.init (List.length it.arg_types) (fun i ->
                 Char.escaped @@ char_of_int (int_of_char 'a' + i))
           in
           SM.add name args acc)
         (ArgOptions.get_intr opts).op_interp
  in

  let empty_ctxt =
    {
      null_checks = opts.ArgOptions.check_null;
      relations;
      o_hints;
      curr_fun = None;
      let_types =
        IntMap.map lift_and_unfold
          side_results.SimpleChecker.SideAnalysis.let_types;
      bif_types = (ArgOptions.get_intr opts).op_interp;
      fenv;
      impl = [];
      havoc_set = P.PathSet.empty;
      fold_iso = side_results.SimpleChecker.SideAnalysis.fold_locs;
      unfold_iso = side_results.SimpleChecker.SideAnalysis.unfold_locs;
      recursive_rel = P.PathMap.empty;
      snapshots = IntMap.empty;
      omit_set;
      pte_rel;
      fn_params;
    }
  in
  let ctxt =
    List.fold_left (fun ctxt fn -> analyze_function fn ctxt) empty_ctxt fns
  in
  let ctxt =
    analyze_main entry_relation main
      {
        ctxt with
        curr_fun = None;
        havoc_set = P.PathSet.empty;
        recursive_rel = P.PathMap.empty;
      }
  in
  (ctxt.relations, ctxt.impl, ctxt.snapshots, start_name, ctxt.omit_set)

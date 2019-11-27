open Sexplib.Std
open Greek
open Std
open Std.StateMonad
module P = Paths

type 'r rel_imm =
  | RAp of 'r
  | RConst of int [@@deriving sexp]

type 'r rel_op =
    Nu
  | RImm of 'r rel_imm [@@deriving sexp]

type ('a,'b) relation = {
  rel_op1: 'a;
  rel_cond: string;
  rel_op2: 'b
} [@@deriving sexp]

type 'r refinement_rel = ('r rel_op,'r rel_imm) relation [@@deriving sexp]

type refine_ap = [
  | `Concr of P.path
  | `Sym of int
] [@@deriving sexp]

(* 
Pred n,l: A predicate symbol with name n over variables l (nu is implicit)
CtxtPred c,n,l: A Preciate symbol with name n over variables l with explicit context c
Top: unconstrained
Const: the constaint constraint
Eq: equality with variable b
*)
type ('c,'r) refinement =
  | Pred of string * 'c
  | CtxtPred of int * string * 'c
  | Top
  | ConstEq of int
  | Relation of 'r refinement_rel
  | And of ('c,'r) refinement * ('c,'r) refinement
  | NamedPred of string * 'c [@@deriving sexp]

type concr_refinement = ((P.concr_ap list * P.concr_ap), P.concr_ap) refinement [@@deriving sexp]

type ownership =
    OVar of int
  | OConst of float[@@deriving sexp]

type ap_symb =
  | SVar of string
  | SProj of int [@@deriving sexp]

type mu_ap =
    MRoot
  | MProj of mu_ap * int
  | MDeref of mu_ap
  | MElem of mu_ap
  | MLen of mu_ap [@@deriving sexp]

type ty_binding = (int * ap_symb) list [@@deriving sexp]

type rec_args = (int * int) list [@@deriving sexp]

type nullity =
  | NUnk
  | NNull
  | NLive [@@deriving sexp]

type concr_nullity = [
  | `NLive
  | `NNull
  | `NVar of int
] [@@deriving sexp]

let join_nullity a b =
  if a <> b then
    NUnk
  else
    a

(* This might be pretty unsafe... *)
let meet_nullity a b =
  match a,b with
  | NUnk,n
  | n,NUnk -> n
  | a,b -> assert (a = b); a

type arr_bind = {len: int; ind: int} [@@deriving sexp]

type ('a,'o,'m,'n) _typ =
  | Int of 'a
  | Ref of ('a,'o,'m,'n) _typ * 'o * 'n
  | Tuple of ty_binding * (('a,'o,'m,'n) _typ) list
  | TVar of int
  | Mu of rec_args * 'm * int * ('a, 'o,'m,'n) _typ
  | Array of arr_bind * 'a * 'o * ('a,'o,'m,'n) _typ
[@@deriving sexp]

type arg_refinment =
  | InfPred of string
  | BuiltInPred of string
  | True[@@deriving sexp]

(* this is not a good type *)
type 'a inductive_preds = {
  pred_symbols: (mu_ap * 'a) list;
  fv_map: (mu_ap * (int list * int list)) list;
} [@@deriving sexp]

type symbolic_refinement = (refine_ap list,refine_ap) refinement [@@deriving sexp]
type typ = (symbolic_refinement,bool,symbolic_refinement inductive_preds,nullity) _typ [@@deriving sexp]
type src_typ = (symbolic_refinement,float,symbolic_refinement inductive_preds,nullity) _typ [@@deriving sexp]
type ftyp = typ [@@deriving sexp]

type 'a _funtype = {
  arg_types: 'a list;
  output_types: 'a list;
  result_type: 'a
}[@@deriving sexp]

type 'a walk_pos = {
  under_mu: bool;
  array: arr_bind list;
  under_ref: bool;
  array_ref: bool;
  rec_args: rec_args;
  olist: 'a list;
}

let empty_pos = {under_mu=false;array = [];under_ref=false;array_ref = false; rec_args = []; olist = []}

type funtype = ftyp _funtype [@@deriving sexp]

let ref_of t1 o n = Ref (t1, o, n)

let rec map_refinement_preds ~rel_arg ~named ~ctxt ~pred r =
  let recurse = map_refinement_preds ~rel_arg ~named ~ctxt ~pred in
  match r with
  | And (r1,r2) -> And (recurse r1, recurse r2)
  | Top
  | ConstEq _ -> r
  | CtxtPred (i,nm,p) -> ctxt i nm p
  | Pred (nm,p) -> pred nm p
  | NamedPred (nm,p) -> named nm p
  | Relation { rel_op1; rel_op2; rel_cond } ->
    let map_imm = function
      | RAp r -> RAp (rel_arg r)
      | RConst c -> RConst c
    in
    Relation {
      rel_op1 = (match rel_op1 with Nu -> Nu | RImm i -> RImm (map_imm i));
      rel_op2 = map_imm rel_op2;
      rel_cond
    }

let rec fold_refinement_args ~rel_arg ~pred_arg a = function
  | And (r1,r2) ->
      let fold = fold_refinement_args ~rel_arg ~pred_arg in
      fold (fold a r1) r2
  | Top -> a
  | ConstEq _ -> a
  | Pred (_,arg)
  | NamedPred (_,arg)
  | CtxtPred (_,_,arg) ->
    pred_arg a arg
  | Relation { rel_op1; rel_op2; _ } ->
    let get_imm a = function
      | RAp r -> rel_arg a r
      | RConst _ -> a
    in
    let a' = get_imm a rel_op2 in
    match rel_op1 with
    | Nu -> a'
    | RImm i -> get_imm a' i

let rec map_refinement f =
  function
  | Int r -> Int (f r)
  | Ref (t,o,n) -> Ref (map_refinement f t,o,n)
  | Tuple (b,tl) -> Tuple (b,(List.map (map_refinement f) tl))
  | Mu (a,fv,v,t) -> Mu (a,fv,v,map_refinement f t)
  | TVar v -> TVar v
  | Array (b,len_r,o,et) ->
    Array (b,f len_r,o,map_refinement f et)

let rec fold_refinements f a = function
  | TVar _ -> a
  | Int r -> f a r
  | Mu (_,_,_,t)
  | Ref (t,_,_) -> fold_refinements f a t
  | Tuple (_,tl) -> List.fold_left (fold_refinements f) a tl
  | Array (_,len_r,_,et) ->
    f (fold_refinements f a et) len_r

let rec to_simple_type = function
  | Ref (t,_,_) -> `Ref (to_simple_type t)
  | Int _ -> `Int
  | Tuple (_,t) -> `Tuple (List.map to_simple_type t)
  | Mu (_,_,v,t) -> `Mu (v, to_simple_type t)
  | TVar v -> `TVar v
  | Array (_,_,_,Int _) ->
    `Array `Int
  | Array _ -> failwith "Non-int arrays unsupported"

let to_simple_funenv env  = StringMap.map (fun { arg_types; result_type; _ } ->
    {
      SimpleTypes.arg_types = List.map to_simple_type arg_types;
      SimpleTypes.ret_type = to_simple_type result_type;
    }) env

let map_ap mapping : refine_ap -> P.concr_ap = function
  | `Sym i -> begin
    try
      List.assoc_opt i mapping |> Option.get
    with
      Invalid_argument _ -> failwith @@ Printf.sprintf "Could not find symbol %d" i
    end
  | `Concr cp -> cp

let partial_map_ap mapping : refine_ap -> refine_ap = function
  | `Sym i -> List.assoc_opt i mapping |> Option.map (fun x -> (x :> refine_ap)) |> Option.value ~default:(`Sym i)
  | `Concr r -> `Concr r

let subst_pv mapping pl =
  let map_ap = map_ap mapping in
  List.map map_ap pl

let map_rel_imm (map_fn: 'a -> 'b) : 'a rel_imm -> 'b rel_imm = function
  | RConst i -> RConst i
  | RAp r -> RAp (map_fn r)

let map_relation (map_fn: 'a -> 'b) ({ rel_op1; rel_cond; rel_op2 }: 'a refinement_rel) =
  let r1 =
    match rel_op1 with
    | Nu -> Nu
    | RImm i -> RImm (map_rel_imm map_fn i)
  in
  let r2 = map_rel_imm map_fn rel_op2 in
  ({ rel_op1 = r1; rel_cond; rel_op2 = r2 }: 'b refinement_rel)

let partial_subst (subst_assoc : (int * [< refine_ap]) list) : (refine_ap list, refine_ap) refinement -> (refine_ap list, refine_ap) refinement =
  let subst_fn = partial_map_ap subst_assoc in
  let subst = List.map subst_fn in
  let rec loop r =
    match r with
    | Pred (i,pv) -> Pred (i,subst pv)
    | CtxtPred (i1,i2,pv) -> CtxtPred (i1,i2, subst pv)
    | Top -> Top
    | Relation rel -> Relation (map_relation subst_fn rel)
    | ConstEq ce -> ConstEq ce
    | And (p1,p2) -> And (loop p1, loop p2)
    | NamedPred (nm,pv) -> NamedPred (nm, subst pv)
  in
  loop

let unfold_gen ~gen ~rmap ~iref:(apply_ref,imap) arg ind_ref id t_in =
  let codom = List.map snd arg in
  (* TODO: I am almost certain these are equal, and we can do away with them *)
  let gen_var_for i (subst,acc) = 
    let fresh_var = gen () in
    ((i,fresh_var)::subst,
      (if List.mem i codom then
        (i,fresh_var)::acc
      else
        acc)),fresh_var
  in
  let do_subst t =
    let rec loop = function
      | Int r -> return @@ Int r
      | TVar a -> return @@ TVar a
      | Mu _ -> failwith "let's not deal with this yet"
      | Ref (t,o,n) ->
        let%bind t' = loop t in
        return @@ Ref (t',o,n)
      | Array ({len;ind},len_r,o,et) ->
        let%bind fresh_len = gen_var_for len in
        let%bind fresh_ind = gen_var_for ind in
        let%bind et' = loop et in
        let len_r' = rmap ([len,fresh_len;ind,fresh_ind]) len_r in
        return @@ Array ({len = fresh_len; ind = fresh_ind},len_r',o,et')
      | Tuple (b,tl) ->
        let%bind b' =
          map_with_accum (fun (i,r) ->
            let%bind fresh_var = gen_var_for i in
            return (fresh_var,r)
          ) b
        in
        let%bind tl' = map_with_accum loop tl in
        return @@ Tuple (b',tl')
    in
    loop t ([],[])
  in
  
  let apply_pred {pred_symbols = pred_map; _} sub_map m_ap r =
    let app' = List.assoc m_ap pred_map |> imap (sub_map @ arg) in
    let outer_sub = rmap sub_map r in
    let r' = apply_ref outer_sub app' in
    let%bind () = mutate @@ fun l -> (m_ap,app')::l in
    return @@ r'
  in
  
  let rec apply pred_map sub_map m_ap t' =
    match t' with
    | TVar t_id -> return @@ TVar t_id
    | Ref (t_,o,n) ->
      let%bind t_app = apply pred_map sub_map (MDeref m_ap) t_ in
      return @@ Ref (t_app, o, n)
    | Mu (_,_,_,_) -> failwith "Nested recursive types are not supported"
    | Tuple (b,tl) ->
      let%bind tl' = mmapi (fun i t_e ->
          apply pred_map sub_map (MProj (m_ap,i)) t_e
        ) tl in
      return @@ Tuple (b,tl')
    | Int r ->
      let%bind r' = apply_pred pred_map sub_map m_ap r in
      return @@ Int r'
    | Array (b,len_r,o,et) ->
      let%bind len_r' = apply_pred pred_map sub_map (MLen m_ap) len_r in
      let%bind et' = apply pred_map sub_map (MElem m_ap) et in
      return @@ Array (b,len_r',o,et')
  in
  let rec loop =
    function
    | TVar t_id when t_id = id ->
      let ((sub_map,new_arg),t') = do_subst t_in in
      let (new_ind_arg,t'') = apply ind_ref sub_map MRoot t' [] in
      let new_fv_map = List.map (fun (mu_ap,(ol,il)) ->
          let update_vars = List.map (fun i ->
              List.assoc i (sub_map @ arg)
            )
          in
          mu_ap,(update_vars ol, update_vars il)
        ) ind_ref.fv_map in
      Mu (new_arg,{pred_symbols = new_ind_arg; fv_map = new_fv_map},id,t'')
    | TVar v -> TVar v
    | Mu (_,_,_,_) -> failwith "Nested recursive types are not supported"
    | Tuple (b,tl) ->
      let tl' = List.map loop tl in
      Tuple (b,tl')
    | Ref (t,o,n) -> Ref (loop t, o,n)
    | Int r -> Int r
    | Array (b,len_r,o,et) ->
      Array (b, len_r, o, loop et)
  in
  loop t_in
  
let unfold ~gen arg ind_ref id t_in =
  let psub sub_arg =
    partial_subst @@ List.map (fun (v,new_v) ->
        (v, `Sym new_v)
      ) sub_arg
  in
  let apply_ref r b = And (r,b) in
  unfold_gen ~gen ~rmap:psub ~iref:(apply_ref,psub) arg ind_ref id t_in

(* TODO: this is the exact same function as compile_bindings... *)
let subst_of_binding root = List.map (fun (i,p) ->
    match p with
    | SProj ind -> (i,P.t_ind root ind)
    | SVar v -> (i, P.var v)
  )

let update_binding_gen tup_b (fv_ap,sym_vals) : ('a * (int * P.concr_ap) list) =
  let added_bindings = List.map (fun (i,_) -> `Sym i) tup_b in
  let fv_ap' = fv_ap @ added_bindings in
  let sym_vals' = tup_b @ sym_vals in
  (fv_ap',sym_vals')

let update_binding path tup_b binding =
  let b_vals = subst_of_binding path tup_b in
  update_binding_gen b_vals binding

let bind_of_arr b root =
  [(b.ind,P.ind root);(b.len,P.len root)]

let fv_of_arr b =
  [ `Sym b.ind; `Sym b.len ]

let ap_is_target target sym_vals ap =
  match ap with
  | `Concr cr_ap -> cr_ap = target
  | `Sym i -> (List.assoc i sym_vals) = target

let filter_fv path sym_vals =
  List.filter (fun free_var -> not @@ ap_is_target path sym_vals free_var)

let rec walk_with_bindings_own ?(pos=empty_pos) ~mu_map ~o_map f root bindings t =
  match t with
  | TVar v -> return @@ TVar v
  | Mu (ar,fv,v,t') ->
    assert (not pos.under_mu);
    let (pre_mu,post_mu) = mu_map in
    let%bind () = pre_mu root ar fv in
    let%bind t'' = walk_with_bindings_own ~pos:{pos with under_mu = true;rec_args = ar} ~o_map ~mu_map f root bindings t' in
    let%bind fv' = post_mu root fv in
    return @@ Mu (ar,fv',v,t'')
  | Int r ->
    let (sym_fv,sym_vals) = bindings in
    let%bind r' = f ~pos root (filter_fv root sym_vals sym_fv,sym_vals) r in
    return @@ Int r'
  | Ref (t',o,n) ->
    let%bind o' = o_map o root in
    let%bind t'' = walk_with_bindings_own ~pos:{pos with under_ref = true; olist = o'::pos.olist} ~o_map ~mu_map f (P.deref root) bindings t' in
    return @@ Ref (t'',o',n)
  | Array (b,len_r,o,et) ->
    let len_path = P.len root in
    let bindings' = update_binding_gen (bind_of_arr b root) bindings in
    let%bind len_r' = f ~pos:{pos with array_ref = true} len_path bindings len_r in
    let%bind o' = o_map o root in
    let%bind et' = walk_with_bindings_own ~pos:{pos with array = b::pos.array; array_ref = true;olist = o'::pos.olist} ~mu_map ~o_map f (P.elem root) bindings' et in
    return @@ Array (b,len_r',o',et')
  | Tuple (b,tl) ->
    let tl_named = List.mapi (fun i t ->
        let nm = P.t_ind root i in
        (nm,t)
      ) tl in
    let bindings' = update_binding root b bindings in
    let rec loop l =
      match l with
      | [] -> return []
      | (nm,t)::tl ->
        let%bind t' = walk_with_bindings_own ~pos ~o_map ~mu_map f nm bindings' t in
        let%bind tl' = loop tl in
        return @@ t'::tl'
    in
    let%bind tl' = loop tl_named in
    return @@ Tuple (b,tl')

let id_mu_map =
  (fun _ _ _ -> return ()),
  (fun _ fv -> return fv)

let id_pred_map = (fun ~pos:_ _ _ r -> return r)

let id_omap = (fun o _ -> return o)

let empty_bindings = ([],[])

let walk_with_bindings ?(o_map=(fun o _ c -> (c,o))) f root bindings t a =
  walk_with_bindings_own ~o_map ~mu_map:id_mu_map f root bindings t a

let walk_with_path ?o_map f root =
  walk_with_bindings ?o_map (fun ~pos p _ r a' ->
    f ~pos p r a'
  ) root ([],[])

let map_with_bindings ?o_map f root bindings t =
  walk_with_bindings ?o_map (fun ~pos p b r () ->
    ((), f ~pos p b r)
  ) root bindings t () |> snd

let fold_with_bindings f root bindings t a =
  walk_with_bindings (fun ~pos p b r a' ->
    (f ~pos p b r a',r)
  ) root bindings t a |> fst

let map_with_path f root t =
  map_with_bindings (fun ~pos p _ r ->
    f ~pos p r) root ([],[]) t


let compile_refinement target subst_assoc =
  let subst_fn = map_ap subst_assoc in
  let subst = subst_pv subst_assoc in
  let rec loop r = 
    match r with
    | Pred (i,pv) -> Pred (i,(subst pv,target))
    | CtxtPred (i1,i2,pv) -> CtxtPred (i1,i2,(subst pv,target))
    | Top -> Top
    | Relation rel -> Relation (map_relation subst_fn rel)
    | ConstEq ce -> ConstEq ce
    | And (p1,p2) -> And (loop p1, loop p2)
    | NamedPred (nm,pv) -> NamedPred (nm,(subst pv,target))
  in loop

let compile_bindings blist root =
  List.map (fun (k,t) ->
    match t with
    | SVar v -> (k,P.var v)
    | SProj i -> (k,P.t_ind root i)
  ) blist

let compile_type_gen =
  let rec compile_loop t1 root bindings =
    match t1 with
    | Int r -> Int (compile_refinement root bindings r)
    | Ref (t,o,n) -> Ref (compile_loop t (P.deref root) bindings,o,n)
    | Tuple (b,tl) ->
      let bindings' = bindings @ (compile_bindings b root) in
      let tl' = List.mapi (fun i t ->
          compile_loop t (P.t_ind root i) bindings'
        ) tl in
      Tuple ([],tl')
    | TVar v  -> TVar v
    | Mu (a,_,v,t) ->
      let compiled_t = compile_loop t root bindings in
      Mu (a,(),v, compiled_t)
    | Array (b,len_r,o,et) ->
      let bindings' = bindings @ [(b.ind,P.ind root); (b.len,P.len root)] in
      let len_rc = compile_refinement (P.len root) bindings len_r in
      Array (b,len_rc,o,compile_loop et (P.len root) bindings')
  in
  compile_loop

let compile_type_path t1 ap = compile_type_gen t1 ap []

let compile_type t1 root =
  compile_type_path t1 @@ P.var root

let refine_ap_to_string = function
  | `Concr cp -> P.to_z3_ident cp
  | `Sym i -> Printf.sprintf "$%d" i


let pp_owner b =
  let open PrettyPrint in
  ps @@ Printf.sprintf "%b" b

let simplify_ref r_in = 
  let rec loop ~ex ~k r =
    match r with
    | Relation _
    | CtxtPred _
    | NamedPred _
    | ConstEq _
    | Pred _ -> k r
    | And (r1,r2) ->
      loop
        ~ex:(fun () ->
          loop ~ex ~k r2)
        ~k:(fun r1' ->
          loop
            ~ex:(fun () -> k r1')
            ~k:(fun r2' -> k @@ And (r1',r2'))
            r2)
        r1
    | Top -> ex ()
  in
  loop ~ex:(fun () -> Top) ~k:(fun r' -> r') r_in

let pp_alist = List.map (fun ap -> PrettyPrint.ps @@ refine_ap_to_string ap)

let rec pp_ref pp_alist =
  let open PrettyPrint in
  let pred_name i = i in
  let print_pred i o ctxt = pb [
      pf "%s(" @@ pred_name i;
      psep_gen (pf ",@ ") @@ [
        ctxt;
        ps nu
      ] @ (pp_alist o);
      pf ")"
    ]
  in
  let pp_rel_imm = function
    | RAp p -> ps @@ refine_ap_to_string (p :> refine_ap)
    | RConst n -> pi n
  in
  let pp_rel_op = function
    | Nu -> ps nu;
    | RImm i -> pp_rel_imm i
  in
  function
  | Pred (i,o) -> print_pred i o @@ ps alpha
  | CtxtPred (c,i,o) -> print_pred i o @@ pi c
  | Top -> ps "T"
  | ConstEq n -> pf "%s = %d" nu n
  | Relation { rel_op1; rel_cond; rel_op2 } ->
    pb [
        pf "%a@ %s@ %a"
          (ul pp_rel_op) rel_op1
          rel_cond
          (ul pp_rel_imm) rel_op2
      ]
  | NamedPred (s,o) ->
    pb [
        pf "%s(" s;
        psep_gen (pf ",@ ") @@ (ps nu)::(pp_alist o);
        ps ")"
      ]
  | And (r1,r2) ->
    pb [
        pp_ref pp_alist r1;
        pf "@ /\\@ ";
        pp_ref pp_alist r2
      ]

let pp_map ff l =
  let open PrettyPrint in
  psep_gen (pf ",@ ")
    (List.map (fun (i,j) ->
      pf "%d -> %d" i j
    ) l) ff

let pp_nullity = function
  | NUnk -> PrettyPrint.ps "?"
  | NLive -> PrettyPrint.ps "!"
  | NNull -> PrettyPrint.ps Greek.bot
    
let pp_type_gen (r_print: string -> 'a -> Format.formatter -> unit) (o_print : 'o -> Format.formatter -> unit) : ('a,'o,'m,'n) _typ -> Format.formatter -> unit =
  let open PrettyPrint in
  let sym_var = pf "$%d" in
  let rec pp_type = function
    | Tuple (b,tl) ->
      let bound_vars = List.filter (fun (_,p) ->
          match p with
          | SProj _ -> true
          | _ -> false
        ) b |> List.map (fun (i,p) ->
            match p with
            | SProj ind -> (ind,i)
            | _ -> assert false
          ) in
      let pp_tl = List.mapi (fun ind t ->
          let pp_t = pp_type t in
          if List.mem_assoc ind bound_vars then
            let bound_name = sym_var @@ List.assoc ind bound_vars in
            pb [
              bound_name; ps ":"; sbrk;
              pp_t
            ]
          else
            pp_t
        ) tl in
      pb [
        ps "(";
        psep_gen (pf ",@ ") pp_tl;
        ps ")"
      ]
    | Int r -> r_print "int" r
    | Array (b,len_r,o,et) ->
      pb [
          ps "[";
          pb [
            ps "(";
            pf "$%d.." b.ind;
            pf "$%d:" b.len;
            r_print "int" len_r;
            ps ")"
          ];
          pf ";@ ";
          pp_type et;
          pf "@ "; o_print o; ps "]"
        ]
    | Ref (t,o,n) ->
      pb [
          pp_type t;
          pf "@ ref%a@ " (ul pp_nullity) n;
          o_print o
        ]
    | TVar v -> pf "'%d" v
    | Mu (map,_, v,t) ->
      pb [
          pf "(%s{%a} '%d.@ " mu pp_map map v;
          pp_type t;
          ps ")"
        ]
  in
  pp_type

let pp_type : typ -> Format.formatter -> unit =
  let open PrettyPrint in
  pp_type_gen (fun k r ->
    pb [
      pf "{%s:%s@ |@ " nu k;
      simplify_ref r |> pp_ref pp_alist;
      ps "}"
    ]) pp_owner

let string_of_type = PrettyPrint.pretty_print_gen_rev pp_type
let string_of_owner = PrettyPrint.pretty_print_gen_rev pp_owner
let string_of_refinement : symbolic_refinement -> string = PrettyPrint.pp_gen_rev (pp_ref pp_alist)

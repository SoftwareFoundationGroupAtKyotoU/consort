open Sexplib.Std
open Greek
open Std

type 'r rel_imm =
  | RAp of 'r
  | RConst of int [@@deriving sexp]

type 'r rel_op =
    Nu
  | RImm of 'r rel_imm [@@deriving sexp]

type 'r refinement_rel = {
  rel_op1: 'r rel_op;
  rel_cond: string;
  rel_op2: 'r rel_imm;
} [@@deriving sexp]

type refine_ap = [
  Paths.concr_ap
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

type concr_refinement = ((Paths.concr_ap list * Paths.concr_ap), Paths.concr_ap) refinement [@@deriving sexp]

type ownership =
    OVar of int
  | OConst of float[@@deriving sexp]

type ap_symb =
  | SVar of string
  | SProj of int [@@deriving sexp]

type ty_binding = (int * ap_symb) list [@@deriving sexp]

type rec_args = (int * int) list [@@deriving sexp]

type nullity = [
  | `NUnk
  | `NNull
  | `NLive
] [@@deriving sexp]

type arr_bind = {len: int; ind: int} [@@deriving sexp]

type ('a,'o) _typ =
  | Int of 'a
  | Ref of ('a,'o) _typ * 'o * nullity
  | Tuple of ty_binding * (('a,'o) _typ) list
  | TVar of int
  | Mu of rec_args * int * ('a, 'o) _typ
  | Array of arr_bind * 'a * 'o * ('a,'o) _typ
[@@deriving sexp]

type arg_refinment =
  | InfPred of string
  | BuiltInPred of string
  | True[@@deriving sexp]

type typ = (((refine_ap list,refine_ap) refinement),ownership) _typ [@@deriving sexp]
type ftyp = (arg_refinment,ownership) _typ[@@deriving sexp]

type 'a _funtype = {
  arg_types: 'a list;
  output_types: 'a list;
  result_type: 'a
}[@@deriving sexp]

type walk_pos = {under_mu: bool; array: arr_bind list; under_ref: bool; array_ref: bool}

type funtype = ftyp _funtype [@@deriving sexp]

let ref_of t1 o n = Ref (t1, o, n)

let rec map_refinement f =
  function
  | Int r -> Int (f r)
  | Ref (t,o,n) -> Ref (map_refinement f t,o,n)
  | Tuple (b,tl) -> Tuple (b,(List.map (map_refinement f) tl))
  | Mu (a,v,t) -> Mu (a,v,map_refinement f t)
  | TVar v -> TVar v
  | Array (b,len_r,o,et) ->
    Array (b,f len_r,o,map_refinement f et)

let rec fold_refinements f a = function
  | TVar _ -> a
  | Int r -> f a r
  | Mu (_,_,t)
  | Ref (t,_,_) -> fold_refinements f a t
  | Tuple (_,tl) -> List.fold_left (fold_refinements f) a tl
  | Array (_,len_r,_,et) ->
    f (fold_refinements f a et) len_r

let rec to_simple_type = function
  | Ref (t,_,_) -> `Ref (to_simple_type t)
  | Int _ -> `Int
  | Tuple (_,t) -> `Tuple (List.map to_simple_type t)
  | Mu (_,v,t) -> `Mu (v, to_simple_type t)
  | TVar v -> `TVar v
  | Array (_,_,_,Int _) ->
    `Array `Int
  | Array _ -> failwith "Non-int arrays unsupported"

let to_simple_funenv env  = StringMap.map (fun { arg_types; result_type; _ } ->
    {
      SimpleTypes.arg_types = List.map to_simple_type arg_types;
      SimpleTypes.ret_type = to_simple_type result_type;
    }) env

let map_ap mapping : refine_ap -> Paths.concr_ap = function
  | `Sym i -> begin
    try
      List.assoc_opt i mapping |> Option.get
    with
      Invalid_argument _ -> failwith @@ Printf.sprintf "Could not find symbol %d" i
    end
  | #Paths.concr_ap as cp -> cp

let partial_map_ap mapping : refine_ap -> refine_ap = function
  | `Sym i -> List.assoc_opt i mapping |> Option.map (fun x -> (x :> refine_ap)) |> Option.value ~default:(`Sym i)
  | r -> r

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

let unfold_gen ~gen ~rmap arg id t_in =
  let codom = List.map snd arg in
  let gen_var_for i (subst,acc) = 
    let fresh_var = gen () in
    fresh_var,(
      (i,fresh_var)::subst,
      (if List.mem i codom then
        (i,fresh_var)::acc
      else
        acc))
  in
  let do_subst t =
    let rec loop ((subst,_) as acc) = function
      | Int r -> (acc,Int (rmap subst r))
      | TVar a -> (acc,TVar a)
      | Mu _ -> failwith "let's not deal with this yet"
      | Ref (t,o,n) ->
        let (acc',t') = loop acc t in
        (acc', Ref (t',o,n))
      | Array ({len;ind},len_r,o,et) ->
        let (fresh_len,acc_len) = gen_var_for len acc in
        let (fresh_ind,acc_ind) = gen_var_for ind acc_len in
        let acc',et' = loop acc_ind et in
        let len_r' = rmap subst len_r in
        acc',Array ({len = fresh_len; ind = fresh_ind},len_r',o,et')
      | Tuple (b,tl) ->
        let (acc',b') =
          map_with_accum acc (fun acc (i,r) ->
            let (fresh_var,acc') = gen_var_for i acc in
            (acc',(fresh_var,r))
          ) b
        in
        let (acc'',tl') = map_with_accum acc' loop tl in
        (acc'',Tuple (b',tl'))
    in
    loop (arg,[]) t
  in
  let rec loop =
    function
    | TVar t_id when t_id = id ->
      let ((_,new_arg),t') = do_subst t_in in
      Mu (new_arg,id,t')
    | TVar v -> TVar v
    | Mu (arg,id,t) -> Mu (arg,id,loop t)
    | Tuple (b,tl) ->
      let tl' = List.map loop tl in
      Tuple (b,tl')
    | Ref (t,o,n) -> Ref (loop t, o,n)
    | Int r -> Int r
    | Array (b,len_r,o,et) ->
      Array (b, len_r, o, loop et)
  in
  loop t_in
  
let unfold ~gen arg id t_in =
  let psub sub_arg =
    partial_subst @@ List.map (fun (v,new_v) ->
        (v, `Sym new_v)
      ) sub_arg
  in
  unfold_gen ~gen ~rmap:psub arg id t_in

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
    | SVar v -> (k,`AVar v)
    | SProj i -> (k,`AProj (root,i))
  ) blist

let compile_type_gen =
  let rec compile_loop t1 root bindings =
    match t1 with
    | Int r -> Int (compile_refinement root bindings r)
    | Ref (t,o,n) -> Ref (compile_loop t (`ADeref root) bindings,o,n)
    | Tuple (b,tl) ->
      let bindings' = bindings @ (compile_bindings b root) in
      let tl' = List.mapi (fun i t ->
          compile_loop t (`AProj (root,i)) bindings'
        ) tl in
      Tuple ([],tl')
    | TVar v  -> TVar v
    | Mu (a,v,t) -> Mu (a,v, compile_loop t root bindings)
    | Array (b,len_r,o,et) ->
      let bindings' = bindings @ [(b.ind,`AInd root); (b.len,`ALen root)] in
      let len_rc = compile_refinement (`ALen root) bindings len_r in
      Array (b,len_rc,o,compile_loop et (`AElem root) bindings')
  in
  compile_loop

let compile_type_path t1 ap = compile_type_gen t1 ap []

let compile_type t1 root =
  compile_type_path t1 @@ `AVar root

let subst_of_binding root = List.map (fun (i,p) ->
    match p with
    | SProj ind -> (i,`AProj (root,ind))
    | SVar v -> (i, `AVar v)
  )

let update_binding_gen tup_b (fv_ap,sym_vals) : ('a * (int * Paths.concr_ap) list) =
  let added_bindings = List.map (fun (i,_) -> `Sym i) tup_b in
  let fv_ap' = fv_ap @ added_bindings in
  let sym_vals' = tup_b @ sym_vals in
  (fv_ap',sym_vals')

let update_binding path tup_b binding =
  let b_vals = subst_of_binding path tup_b in
  update_binding_gen b_vals binding

let bind_of_arr b root =
  [(b.ind,`AInd root);(b.len,`ALen root)]

let fv_of_arr b =
  [ `Sym b.ind; `Sym b.len ]


let ap_is_target target sym_vals ap =
  match ap with
  | #Paths.concr_ap as cr_ap -> cr_ap = target
  | `Sym i -> (List.assoc i sym_vals) = target

let filter_fv path sym_vals =
  List.filter (fun free_var -> not @@ ap_is_target path sym_vals free_var)

let rec walk_with_bindings_own ?(pos={under_mu=false;array = [];under_ref=false;array_ref = false}) ~o_map f root bindings t a =
  match t with
  | TVar v -> (a,TVar v)
  | Mu (ar,v,t') ->
    let (a',t'') = walk_with_bindings_own ~pos:{pos with under_mu = true} ~o_map f root bindings t' a in
    (a', Mu (ar,v,t''))
  | Int r ->
    let (sym_fv,sym_vals) = bindings in
    let (a',r') = f ~pos root (filter_fv root sym_vals sym_fv,sym_vals) r a in
    (a',Int r')
  | Ref (t',o,n) ->
    let (a',t'') = walk_with_bindings_own ~pos:{pos with under_ref = true} ~o_map f (`ADeref root) bindings t' a in
    let (a'',o') = o_map a' o in
    (a'',Ref (t'',o',n))
  | Array (b,len_r,o,et) ->
    let len_path = `ALen root in
    let bindings' = update_binding_gen (bind_of_arr b root) bindings in
    let (a',len_r') = f ~pos:{pos with array_ref = true} len_path bindings len_r a in
    let (a'',o') = o_map a' o in
    let (a''',et') = walk_with_bindings_own ~pos:{pos with array = b::pos.array; array_ref = true} ~o_map f (`AElem root) bindings' et a'' in
    (a''', Array (b,len_r',o',et'))
  | Tuple (b,tl) ->
    let tl_named = List.mapi (fun i t ->
        let nm = Paths.t_ind root i in
        (nm,t)
      ) tl in
    let bindings' = update_binding root b bindings in
    let rec loop a_accum l =
      match l with
      | [] -> (a_accum,[])
      | (nm,t)::tl ->
        let (acc',t') = walk_with_bindings_own ~pos ~o_map f nm bindings' t a_accum in
        let (acc'',tl') = loop acc' tl in
        (acc'',t'::tl')
    in
    let (a',tl') = loop a tl_named in
    (a',Tuple (b,tl'))

let walk_with_bindings ?(o_map=(fun c o -> (c,o))) f root bindings t a =
  walk_with_bindings_own ~o_map f root bindings t a

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

let rec update_nth l i v =
  match l with
  | h::t ->
    if i = 0 then
      v::t
    else
      h::(update_nth t (i - 1) v)
  | [] -> raise @@ Invalid_argument "Bad index"

let map_ap_with_bindings (ap : [< Paths.concr_ap]) fvs f gen =
  let rec inner_loop ap' c =
    match ap' with
    | `ALen _
    | `AInd _
    | `APre _ -> failwith "V illegal"
    | `AElem ap ->
      inner_loop ap (fun b t' ->
          match t' with
          | Array (ba,l,o,t) ->
            let (a',mapped) = c (update_binding_gen (bind_of_arr ba ap) b) t in
            (a',Array (ba,l,o,mapped))
          | _ -> failwith "Invalid type for Elem"
        )
    | `AVar v -> c (fvs,[]) (gen v)
    | `ADeref ap ->
      inner_loop ap (fun b t' ->
          match t' with
          | Ref (t'',o,n) ->
            let (a',mapped) = c b t'' in
            (a',Ref (mapped,o,n))
          | _ -> failwith "Invalid type for AP"
        )
    | `AProj (ap,i) ->
      inner_loop ap (fun b t' ->
          match t' with
          | Tuple (bind,tl) ->
            let t_sub = List.nth tl i in
            let (a',mapped) = c (update_binding ap bind b) t_sub in
            (a',Tuple (bind, update_nth tl i mapped))
          | _ -> failwith @@ Printf.sprintf "Invalid type for proj AP"
        )
  in
  inner_loop ap f

let map_ap ap f gen =
  map_ap_with_bindings ap [] (fun _ t -> (f t,t)) gen |> fst

let refine_ap_to_string = function
  | #Paths.concr_ap as cp -> Paths.to_z3_ident cp
  | `Sym i -> Printf.sprintf "$%d" i


let pp_owner =
  let open PrettyPrint in
  function
  | OVar o -> ps @@ Printf.sprintf "$o%d" o
  | OConst f -> ps @@ Printf.sprintf "%f" f

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

let rec pp_ref =
  let open PrettyPrint in
  let pred_name i = i in
  let pp_alist o = List.map (fun ap -> ps @@ refine_ap_to_string ap) o in
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
        pp_ref r1;
        pf "@ /\\@ ";
        pp_ref r2
      ]

let pp_map () l =
  let open PrettyPrint in
  psep_gen (pf ",@ ") @@
    List.map (fun (i,j) ->
      pf "%d -> %d" i j
    ) l
    
let pp_type_gen (r_print: string -> 'a -> Format.formatter -> unit) (o_print : 'o -> Format.formatter -> unit) : ('a,'o) _typ -> Format.formatter -> unit =
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
    | Ref (t,o,_) ->
      pb [
          pp_type t;
          pf "@ ref@ ";
          o_print o
        ]
    | TVar v -> pf "'%d" v
    | Mu (map,v,t) ->
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
      simplify_ref r |> pp_ref;
      ps "}"
    ]) pp_owner

let string_of_type = PrettyPrint.pretty_print_gen_rev pp_type
let string_of_owner = PrettyPrint.pretty_print_gen_rev pp_owner

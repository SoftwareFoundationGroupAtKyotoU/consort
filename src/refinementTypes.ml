(** Refinement types are currently used in the inline assume
   statements (to specify the invariants that must hold on non-deterministic input)
   and in the types for intrinsics (see that file) *)

open Sexplib.Std
open Greek

module P = Paths

type rel_imm =
  | RAp of P.concr_ap (** An access path given by the type parameter 'r *)
  | RConst of int [@@deriving sexp]

type rel_op =
    Nu (** In the context of relating a specific value, refers to the value being refined *)
  | RImm of rel_imm [@@deriving sexp]

(** A logical relations (think comparison) between two values. rel_cond is the string representation of the
   relation symbol *)
type ('a,'b) relation = {
  rel_op1: 'a;
  rel_cond: string;
  rel_op2: 'b
} [@@deriving sexp]

type refinement_rel = (rel_op, rel_imm) relation [@@deriving sexp]

type refine_ap = P.path

(** A refinement on a particular value *)
type refinement =
  | Top (** The value is completely unconstrained *)
  | ConstEq of int (** The value is exactly equal to n *)
  | Relation of refinement_rel (** The value is constrained according to the relation *)
  | And of refinement * refinement (** The value is constrained by both sub refinements *)
  | NamedPred of string * (P.concr_ap list) (** The value is constrained according to the SMT function with the given name. The name of the
                                               value being refined is given implicitly as the first argument to the function; the paths listed
                                               in the second argument are given as all remaining arguments *) [@@deriving sexp]

type concr_refinement = refinement [@@deriving sexp]

type ownership = float [@@deriving sexp]

(** The type skeleton for refinement type, parameterized by the type of refinements *)
type 'a _typ =
  | Int of 'a
  | Ref of 'a _typ * ownership * bool
  | Tuple of 'a _typ list
  | Array of 'a * ownership * 'a _typ
[@@deriving sexp]

(** Refinement types with refinements defined by concr_refinement *)
type typ = concr_refinement _typ [@@deriving sexp]
type ftyp = typ [@@deriving sexp]

type 'a _funtype = {
  arg_types: 'a list;
  output_types: 'a list;
  result_type: 'a
}[@@deriving sexp]

type funtype = ftyp _funtype [@@deriving sexp]

let get_args_length fn = List.length fn.arg_types

let rec to_simple_type = function
  | Ref (t,_,_) -> `Ref (to_simple_type t)
  | Int _ -> `Int
  | Tuple t -> `Tuple (List.map to_simple_type t)
  | Array (_,_,Int _) ->
    `Array `Int
  | Array _ -> failwith "Non-int arrays unsupported"

let to_simple_funenv env  = StringMap.map (fun { arg_types; result_type; _ } ->
    {
      SimpleTypes.arg_types = List.map to_simple_type arg_types;
      SimpleTypes.ret_type = to_simple_type result_type;
    }) env

let pp_owner b =
  let open PrettyPrint in
  ps @@ Printf.sprintf "%b" b

let simplify_ref r_in = 
  let rec loop ~ex ~k r =
    match r with
    | Relation _
    | NamedPred _
    | ConstEq _ -> k r
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

let pp_alist = List.map (fun ap -> PrettyPrint.ps @@ P.to_z3_ident ap)

let rec pp_ref pp_alist =
  let open PrettyPrint in
  let pp_rel_imm = function
    | RAp p -> ps @@ P.to_z3_ident p
    | RConst n -> pi n
  in
  let pp_rel_op = function
    | Nu -> ps nu;
    | RImm i -> pp_rel_imm i
  in
  function
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
    
let pp_type_gen (r_print: string -> 'a -> Format.formatter -> unit) : 'a _typ -> Format.formatter -> unit =
  let open PrettyPrint in
  let rec pp_type = function
    | Tuple tl ->
      let pp_tl = List.map (fun t ->
          pp_type t
        ) tl in
      pb [
        ps "(";
        psep_gen (pf ",@ ") pp_tl;
        ps ")"
      ]
    | Int r -> r_print "int" r
    | Array (len_r,o,et) ->
      pb [
          ps "[";
          pb [
            ps "(";
            r_print "int" len_r;
            ps ")"
          ];
          pf ";@ ";
          pp_type et;
          pf "@ %f]" o
        ]
    | Ref (t,o,_) ->
      pb [
          pp_type t;
          pf "@ ref@ %f" o;
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
    ])

let string_of_type = PrettyPrint.pretty_print_gen_rev pp_type
let string_of_owner = PrettyPrint.pretty_print_gen_rev pp_owner
let string_of_refinement : concr_refinement -> string = PrettyPrint.pp_gen_rev (pp_ref pp_alist)

type root = [
  (* name, pre, null? *)
  | `AVar of string * bool * bool
  | `ARet of bool
] [@@deriving sexp]

type 'a _const_ap = [
  | root
  |  `ALen of 'a
  | `AProj of 'a * int
] [@@deriving sexp]
type const_ap = const_ap _const_ap [@@deriving sexp]

type 'a t_templ = [
  'a _const_ap
| `ADeref of 'a
| `AElem of 'a
| `AInd of 'a
] [@@deriving sexp]

type concr_ap = [
  | concr_ap t_templ
] [@@deriving sexp]

val to_z3_ident :
  ([< 'a t_templ ]
   as 'a) ->
  string
val has_prefix : ([< 'a t_templ] as 'a) -> 'a -> bool
val pre :
  ([< 'a t_templ > `ADeref `AProj `ALen `AVar ] as 'a) ->
  'a
    
val t_ind : 'a -> 'b -> [> `AProj of 'a * 'b ]
val elem : 'a -> [> `AElem of 'a]
val deref : 'a -> [> `ADeref of 'a ]
val var: string -> [> `AVar of string * bool * bool ]
val arg : int -> [> `AVar of string * bool * bool ]
val arg_name : int -> string
val len : 'a -> [> `ALen of 'a]
val ind : 'a -> [> `AInd of 'a]
val ret : [> `ARet of bool ]

val is_pre : ([< 'a t_templ >  `ADeref `AProj `AVar] as 'a) -> bool
val is_const_ap :
  ([< 'a t_templ > `AProj `ADeref `AVar ] as 'a) ->
  bool
val has_root :
  string ->
  ([< 'a t_templ ] as 'a) ->
  bool
val has_root_p :
  (string -> bool) ->
  ([< 'b t_templ ] as 'b) ->
  bool

val map_root :
  (string -> string) -> ([< 'b t_templ > `ADeref `AElem `ALen `AProj `AVar `ARet `AInd] as 'b) -> 'b

val is_array_path:
  ([< 'a t_templ > `ADeref `AElem `AInd `ALen `AProj ] as 'a) -> bool

val unsafe_get_root : ([< 'b t_templ > `AVar] as 'b) -> string

val compare : concr_ap -> concr_ap -> int
  
module PathSet : Set.S with type elt = concr_ap
module PathMap : Map.S with type key = concr_ap
module PathOrd : Set.OrderedType with type t = concr_ap

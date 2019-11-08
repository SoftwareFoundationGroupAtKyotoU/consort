type 'a _const_ap = [
  `ALen of 'a
| `APre of string
| `ARet (* the return type *)
| `AProj of 'a * int
| `AVar of string
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
  ([< 'a t_templ > `ADeref `APre `AProj `ALen ] as 'a) ->
  'a
    
val t_ind : 'a -> 'b -> [> `AProj of 'a * 'b ]
val elem : 'a -> [> `AElem of 'a]
val deref : 'a -> [> `ADeref of 'a ]
val var: string -> [> `AVar of string ]
val arg : int -> [> `AVar of string ]
val arg_name : int -> string
val len : 'a -> [> `ALen of 'a]
val ind : 'a -> [> `AInd of 'a]

val is_pre : ([< 'a t_templ > `APre `ADeref `AProj] as 'a) -> bool
val is_const_ap :
  ([< 'a t_templ > `APre `AProj `ADeref ] as 'a) ->
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
  (string -> string) -> ([< 'b t_templ > `ADeref `AElem `ALen `APre `AProj `AVar `ARet `AInd] as 'b) -> 'b

val is_array_path:
  ([< 'a t_templ > `ADeref `AElem `AInd `ALen `AProj ] as 'a) -> bool

val unsafe_get_root : ([< 'b t_templ > `AVar] as 'b) -> string

val compare : concr_ap -> concr_ap -> int
  
module PathSet : Set.S with type elt = concr_ap
module PathMap : Map.S with type key = concr_ap
module PathOrd : Set.OrderedType with type t = concr_ap

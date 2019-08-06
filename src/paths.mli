type 'a _const_ap =
  [ `ALen of 'a | `APre of string | `AProj of 'a * int | `AVar of string ] [@@deriving sexp]
type const_ap = const_ap _const_ap [@@deriving sexp]

type 'a t_templ = [
  'a _const_ap
| `ADeref of 'a
| `AElem of 'a
| `AInd of 'a
]


type concr_ap = [
  | concr_ap t_templ
] [@@deriving sexp]

val to_z3_ident :
  ([< 'a t_templ ]
   as 'a) ->
  string
    
val pre :
  ([< 'a t_templ > `ADeref `APre `AProj ] as 'a) ->
  'a
val t_ind : 'a -> 'b -> [> `AProj of 'a * 'b ]
val is_const_ap :
  ([< 'a t_templ ] as 'a) ->
  bool
val has_root :
  string ->
  ([< 'a t_templ ] as 'a) ->
  bool
val has_root_p :
  (string -> bool) ->
  ([< 'b t_templ ] as 'b) ->
  bool
    
module PathSet : Set.S with type elt = concr_ap

type suff = [`Len | `Ind | `Elem | `None | `Null ] [@@deriving sexp]

type root = private
  | Pre of string
  | Var of string
  | Ret
  | T [@@deriving sexp]

type steps = [
  | `Deref
  | `Proj of int
] [@@deriving sexp]

type path = private root * steps list * suff [@@deriving sexp]
type concr_ap = path [@@deriving sexp]

val to_z3_ident : path ->  string
val has_prefix : prefix:path -> path -> bool
val pre : path -> path

val to_string : path -> string

val t_ind : path -> int -> path
val elem : path -> path
val deref : path -> path
val var: string -> path
val arg : int -> path
val arg_name : int -> string
val len : path -> path
val ind : path -> path
val ret : path

val is_pre : path -> bool
val is_root : path -> bool
val is_const_ap : path -> bool
val has_root : string -> path -> bool
val has_root_p : (string -> bool) -> path -> bool

val template : path

val is_template : path -> bool

val root_at : child:path -> parent:path -> path

val parent : path -> path

val map_root : (string -> string) -> path -> path

val to_null : path -> path
val is_nullity : path -> bool

val is_array_path : path -> bool
val unsafe_get_root : path -> string

val compare : path -> path -> int

val tail : path -> [`Null | `Deref | `Proj of int | `Len | `Elem | `Ind ] option

module PathSet : Std.PRINTSET with type elt = path
module PathMap : Map.S with type key = path
module PathOrd : Set.OrderedType with type t = path

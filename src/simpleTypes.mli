type r_typ = [
  | `Int
  | `TVar of int
  | `Tuple of r_typ list
  | `Ref of r_typ
  | `Mu of int * r_typ
  | `Array of a_typ
] and a_typ = [ `Int ][@@deriving sexp]

type 'a _funtyp = {
  arg_types: 'a list;
  ret_type: 'a
}

type funtyp = r_typ _funtyp

val unfold_simple_type : int -> r_typ -> r_typ
val type_to_string: r_typ -> string
val fntype_to_string: funtyp -> string

type r_typ = [
  | `Int
  | `TVar of int
  | `Tuple of r_typ list
  | `Ref of r_typ
  | `Mu of int * r_typ
  | `Array of a_typ
] and a_typ = [ `Int ]

type funtyp = {
  arg_types: r_typ list;
  ret_type: r_typ
}

val type_to_string: r_typ -> string
val fntype_to_string: funtyp -> string

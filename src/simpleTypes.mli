type r_typ = [
  | `Int
  | `Ref of record_t
] and record_t = r_typ list

type funtyp = {
  arg_types: r_typ list;
  ret_type: r_typ
}

val type_to_string: r_typ -> string
val fntype_to_string: funtyp -> string

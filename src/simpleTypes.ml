type r_typ = [
  | `Int
  | `IntRef
]

type funtyp = {
  arg_types: r_typ list;
  ret_type: r_typ
}


let type_to_string = function
  | `Int -> "int"
  | `IntRef -> "int ref"

let fntype_to_string { arg_types; ret_type} =
  Printf.sprintf "(%s) -> %s" 
    (String.concat ", " @@ List.map type_to_string arg_types) @@
    type_to_string ret_type
  

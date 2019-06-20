type r_typ = [
  | `Int
  | `Ref of record_t
] and record_t = r_typ list

type funtyp = {
  arg_types: r_typ list;
  ret_type: r_typ
}


let rec type_to_string = function
  | `Int -> "int"
  | `Ref t -> Printf.sprintf "(%s) ref" @@ String.concat ", " @@ List.map type_to_string t

let fntype_to_string { arg_types; ret_type} =
  Printf.sprintf "(%s) -> %s" 
    (String.concat ", " @@ List.map type_to_string arg_types) @@
    type_to_string ret_type
  

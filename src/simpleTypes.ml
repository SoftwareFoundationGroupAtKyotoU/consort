type r_typ = [
  | `Int
  | `TVar of int
  | `Tuple of r_typ list
  | `Ref of r_typ
  | `Mu of int * r_typ
]

type funtyp = {
  arg_types: r_typ list;
  ret_type: r_typ
}


let rec type_to_string = function
  | `Int -> "int"
  | `Ref (`Mu _ as t) -> Printf.sprintf "(%s) ref" @@ type_to_string t
  | `Ref t -> Printf.sprintf "%s ref" @@ type_to_string t
  | `Tuple tl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map type_to_string tl
  | `Mu (v,t) -> Printf.sprintf "%s '%d.%s" Greek.mu v @@ type_to_string t
  | `TVar v -> Printf.sprintf "'%d" v

let fntype_to_string { arg_types; ret_type} =
  Printf.sprintf "(%s) -> %s" 
    (String.concat ", " @@ List.map type_to_string arg_types) @@
    type_to_string ret_type
  

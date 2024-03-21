open Sexplib.Std

type r_typ = [
  | `Int
  | `TVar of int
  | `Tuple of r_typ list
  | `Ref of r_typ
  | `Array of a_typ
  | `IntList
]
and a_typ = [ `Int ] [@@deriving sexp]

type 'a _funtyp = {
  arg_types: 'a list;
  ret_type: 'a
}

type funtyp = r_typ _funtyp

let rec type_to_string = function
  | `Int -> "int"
  | `Ref t -> Printf.sprintf "%s ref" @@ type_to_string t
  | `Tuple tl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map type_to_string tl
  | `TVar v -> Printf.sprintf "'%d" v
  | `Array at -> Printf.sprintf "[%s]" @@ array_type_to_string at
  | `IntList -> "int list"
and array_type_to_string = function
  | `Int -> "int"

let fntype_to_string { arg_types; ret_type} =
  Printf.sprintf "(%s) -> %s" 
    (String.concat ", " @@ List.map type_to_string arg_types) @@
    type_to_string ret_type
  

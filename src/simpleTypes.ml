open Sexplib.Std

type r_typ = [
  | `Int
  | `TVar of int
  | `Tuple of r_typ list
  | `Ref of r_typ
  | `Mu of int * r_typ
  | `Array of a_typ
  | `Lock of (r_typ StringMap.t)
  | `ThreadID of (r_typ StringMap.t)
]
and a_typ = [ `Int ] 
[@@deriving sexp]

type 'a _funtyp = {
  arg_types: 'a list;
  ret_type: 'a
}

type funtyp = r_typ _funtyp


let rec type_to_string = function
  | `Int -> "int"
  | `Ref t -> Printf.sprintf "%s ref" @@ type_to_string t
  | `Tuple tl -> Printf.sprintf "(%s)" @@ String.concat ", " @@ List.map type_to_string tl
  | `Mu (v,t) -> Printf.sprintf "(%s '%d.%s)" Greek.mu v @@ type_to_string t
  | `TVar v -> Printf.sprintf "'%d" v
  | `Array at -> Printf.sprintf "[%s]" @@ array_type_to_string at
  | `Lock pte -> 
      let l = StringMap.fold (fun x t l -> (x ^ ": " ^ type_to_string t) :: l) pte [] in
      Printf.sprintf "(%s)lock" @@ String.concat ", " l
  | `ThreadID pte ->
      let l = StringMap.fold (fun x t l -> (x ^ ": " ^ type_to_string t) :: l) pte [] in
      Printf.sprintf "(%s)tid" @@ String.concat ", " l
and array_type_to_string = function
  | `Int -> "int"

let fntype_to_string { arg_types; ret_type} =
  Printf.sprintf "(%s) -> %s" 
    (String.concat ", " @@ List.map type_to_string arg_types) @@
    type_to_string ret_type
  

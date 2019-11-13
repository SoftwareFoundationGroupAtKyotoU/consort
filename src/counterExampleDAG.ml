type nodetype =
  | Update of string * int
  | Let of string * int
  | Seq of string * int
  | Assign of string * int
  | Assert of string * int
  | Alias of string * int
  | If of string * int
  | Var of string * int
  | Annot of string * int
  | False
  | Goal
  | CallIn of string
  | CallOut of string

let show_nodetype = function
  | Update (name, id) ->
      Printf.sprintf "%s-%d-update" name id
  | Let (name, id) ->
      Printf.sprintf "%s-%d-let" name id
  | Seq (name, id) ->
      Printf.sprintf "%s-%d-seq" name id
  | Assign (name, id) ->
      Printf.sprintf "%s-%d-assign" name id
  | Assert (name, id) ->
      Printf.sprintf "%s-%d-assert" name id
  | Alias (name, id) ->
      Printf.sprintf "%s-%d-alias" name id
  | If (name, id) ->
      Printf.sprintf "%s-%d-ifz" name id
  | Var (name, id) ->
      Printf.sprintf "%s-%d-var" name id
  | Annot (name, id) ->
      Printf.sprintf "%s-%d-$gamma" name id
  | False ->
      "FALSE"
  | Goal ->
      "start"
  | CallIn name ->
      name ^ "-in"
  | CallOut name ->
      name ^ "-out"

type node = {id: int; ty: nodetype; args: int list; dst: int list}

type intlist = int list 
let show_intlist y = 
  let rec sub =
  function 
    | [] -> "" 
    | l :: ls -> (string_of_int l ) ^"; " ^ (sub ls) 
  in
  "[" ^ (sub y) ^ "]"

let show_node {id; ty; args; _} =
  Printf.sprintf "%d %s %s" id (show_nodetype ty) (show_intlist args)

let show_node_dst {id; ty; args; dst} = 
  Printf.sprintf "%d %s %s -> %s" id (show_nodetype ty) (show_intlist args) (show_intlist dst)


type graph = node list

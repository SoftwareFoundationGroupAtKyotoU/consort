module OI = OwnershipInference
module P = Paths
open PrettyPrint


type ast_nodetype =
  | Update
  | Let
  | Seq
  | Assign
  | Assert
  | Alias
  | If
  | IfNull
  | Var
  | Annot

type nodetype =
  Ast of ast_nodetype * string * int
  | CallIn of string
  | CallOut of string
  | Mu
  | False
  | Goal

let show_ast_nodetype s =
  match s with
  | Update ->
      "update"
  | Let ->
      "let"
  | Seq ->
      "seq"
  | Assign ->
      "assign"
  | Assert ->
      "assert"
  | Alias ->
      "alias"
  | If ->
      "ifz"
  | IfNull ->
      "ifnull"
  | Var ->
      "var"
  | Annot ->
      "$gamma"

let pp_nodetype = function
  | Ast (ast_node, name, e_id) ->
      ps @@ Printf.sprintf "%s-%d-%s" name e_id @@ show_ast_nodetype ast_node
  | CallIn name ->
      ps (name ^ "-in")
  | CallOut name ->
      ps (name ^ "-out")
  | False -> 
      ps "false"
  | Goal -> 
      ps "goal"
  | Mu -> 
      ps "mu"



type dst_type = int list

let pp_dst x = psep "," (List.map pi x)

(* 
  A graph given by backend solver.
  int(id of start(main(0)) node) * int(id of end(FALSE) node) * others
*)

type node = {id: int; ty: nodetype; args: int list; dst: dst_type}
type graph = node list

let pp_node node = 
    pf "%d: %a(%a) -> %a" node.id (ul pp_nodetype) node.ty (ul pp_dst) node.args (ul pp_dst) node.dst


let get_goal = List.find (fun x -> x.ty = Goal)
let get_false = List.find (fun x -> x.ty = False)
let get_node (g : graph) i = List.find (fun x -> i = x.id) g

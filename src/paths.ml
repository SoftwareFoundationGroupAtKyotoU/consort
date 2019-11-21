open Sexplib.Std
open Std

type suff = [`Len | `Ind | `Elem | `None | `Null ] [@@deriving sexp]

type root = 
  | Pre of string
  | Var of string
  | Ret of bool
  | Summ of string
  | T [@@deriving sexp]

type steps = [
  | `Deref
  | `Proj of int
] [@@deriving sexp]

type path = root * steps list * suff [@@deriving sexp]

type concr_ap = path [@@deriving sexp]

let root_to_string = function
  | Pre v -> Printf.sprintf "%s!old" v
  | Ret b -> Printf.sprintf "$ret%s" (if b then "!summ" else "")
  | Summ v -> Printf.sprintf "%s!summ" v
  | Var v -> v
  | T -> "$$"

let string_of_suff = function
  | `Null -> "?null"
  | `Len -> "!len"
  | `None -> ""
  | `Ind -> "?ind"
  | `Elem -> "->$i"
  | `Summ -> "?summ"

let to_z3_ident (root,steps,suff) =
  let st = List.fold_left (fun acc s ->
      match s with
      | `Deref -> "->*" ^ acc
      | `Proj i -> Printf.sprintf "->%d%s" i acc
    ) (string_of_suff suff) steps in
  (root_to_string root) ^ st

let to_string = to_z3_ident

let pre (root,step,suff) =
  match root with
  | Summ _
  | T
  | Ret _ -> failwith "illegal"
  | Pre _ -> (root,step,suff)
  | Var v ->
    match suff with
    | `Len | `None | `Null -> (Pre v,step,suff)
    | _ -> failwith "illegal"

let check_extend step (root,steps,suff) =
  if suff <> `None then
    failwith @@ Printf.sprintf !"Cannot extend terminal path (curr %{sexp:suff})" suff
  else
    (root,step::steps,suff)

let set_suff suff' (root,steps,suff) =
  if suff <> `None then
    failwith @@ Printf.sprintf !"Cannot extend terminal path (new %{sexp:suff}) (curr %{sexp:suff})" suff' suff
  else
    match root,suff' with
    | Pre _,(`Null | `Len) -> (root, steps,suff')
    | _,_  -> (root, steps, suff')

let t_ind p i =
  check_extend (`Proj i) p

let deref = check_extend `Deref

let var v = (Var v,[],`None)

let ret = (Ret false, [],`None)
let elem = set_suff `Elem
let ind = set_suff `Ind
let len = set_suff `Len
let arg_name = Printf.sprintf "$%d"
let arg i = var @@ arg_name i

let template = (T, [], `None)

let summ (root, steps, suff) =
  match root with
  | Ret true
  | Summ _ -> (root, steps, suff)
  | T
  | Ret false -> (Ret true, steps, suff)
  | Var v -> (Summ v, steps, suff)
  | Pre _ -> failwith "illegal"

let to_concrete (root, steps, suff) =
  match root with
  | T
  | Pre _ -> failwith "illegal"
  | Ret false
  | Var _ -> (root, steps, suff)
  | Summ v -> (Var v, steps, suff)
  | Ret true -> (Ret false, steps, suff)

let is_summ (d,_,_) = match d with | Summ _ -> true | _ -> false

let map_root f (root,steps,suff) =
  match root with
  | Var v -> (Var (f v), steps, suff)
  | Pre v -> (Pre (f v), steps, suff)
  | Ret b -> (Ret b,steps, suff)
  | Summ v -> (Summ (f v), steps, suff)
  | T -> failwith "illegal"

let is_array_path (_,_, suff) =
  suff = `Len || suff = `Ind || suff = `Elem

let is_pre (r,_,_) =
  match r with
  | Pre _ -> true
  | _ -> false

let has_prefix ~prefix:(pr,ps,psuff) (rr,rs,rsuff) =
  if pr <> rr then
    false
  else if (rsuff <> `None) then
    (psuff = `None || rsuff = psuff) && ps = rs
  else if psuff <> `None then
    false
  else
    (* roots match, no suffixes *)
    let plen = List.length ps in
    let rlen = List.length rs in
    if plen > rlen then
      false
    else
      let rs_chop = IntExt.fold List.tl rs (rlen - plen) in
      rs_chop = ps

let has_root_p p (root,_,_) =
  match root with
  | Summ v
  | Pre v
  | Var v -> p v
  | Ret _ -> false
  | T -> false

let has_root s = has_root_p ((=) s)

let is_const_ap (root,steps,suff) =
  match root with
  | Summ _
  | Var _
  | Pre _ ->
    (List.for_all ((<>) `Deref) steps) && (suff <> `Elem) && (suff <> `Ind)
  | Ret _ -> false
  | T -> failwith "illegal"

let compare = Stdlib.compare

let to_null = set_suff `Null
let is_nullity (_,_,l) = l = `Null

let unsafe_get_root (v,_,_) = match v with
  | Var n -> n
  | _ -> failwith "Not rooted in var"

let parent (p,suff,fl) =
  match suff,fl with
  | [],`None -> raise @@ Invalid_argument "at root"
  | _::t,`None -> (p,t,`None)
  | _,_ -> (p,suff,`None)

let root_at ~child:(r,steps,suff) ~parent:(root,steps2,suff2) =
  let () =
    match r with
    | T -> ()
    | _ -> failwith "already rooted path"
  in
  if suff2 <> `None then
    failwith "Cannot extend terminal path"
  else
    (root, steps @ steps2, suff)

let is_root (_,l,f) = l = [] && f = `None

type tail_ret = [`Null | `Deref | `Proj of int | `Len | `Elem | `Ind ]
type inh_tags = [`Len | `Null | `Ind | `Elem ]

let tail (_,l,f) =
  match l,f with
  | h::_,`None -> Some (h :> tail_ret)
  | [],`None -> None
  | _,(#inh_tags as cr) -> Some cr

module PathOrd = struct
  type t = path
  let compare = compare
end

module PathSet = Std.WithBind(Set.Make(PathOrd))
module PathMap = Map.Make(PathOrd)

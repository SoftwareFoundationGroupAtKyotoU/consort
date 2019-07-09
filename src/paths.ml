open Sexplib.Std

type 'a _const_ap = [
  `AVar of string
| `AProj of 'a * int
] [@@deriving sexp]

type const_ap = const_ap _const_ap [@@deriving sexp]

type concr_ap = [
  concr_ap _const_ap
  | `ADeref of concr_ap
] [@@deriving sexp]
    
let rec to_z3_ident = function
  | `ADeref d -> Printf.sprintf "%s->*" @@ to_z3_ident d
  | `AProj (a,i) -> Printf.sprintf "%s->%d" (to_z3_ident a) i
  | `AVar v -> v

let t_ind a i = `AProj (a,i)

let rec is_const_ap = function
  | `AVar _ -> true
  | `AProj (ap,_) -> is_const_ap ap
  | `ADeref _ -> false

let rec has_root v = function
  | `AVar v' -> v = v'
  | `ADeref ap
  | `AProj (ap,_) -> has_root v ap

let rec has_root_p p = function
  | `AVar v -> p v
  | `ADeref ap
  | `AProj (ap,_) -> has_root_p p ap

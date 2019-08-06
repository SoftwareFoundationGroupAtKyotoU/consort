open Sexplib.Std

type 'a _const_ap = [
  | `AVar of string
  | `ALen of 'a
  | `AProj of 'a * int
  | `APre of string
] [@@deriving sexp]

type const_ap = const_ap _const_ap [@@deriving sexp]

type concr_ap = [
  |  concr_ap _const_ap
  | `ADeref of concr_ap
  | `AElem of concr_ap
  | `AInd of concr_ap
] [@@deriving sexp]

let rec to_z3_ident = function
  | `ADeref d -> Printf.sprintf "%s->*" @@ to_z3_ident d
  | `AProj (a,i) -> Printf.sprintf "%s->%d" (to_z3_ident a) i
  | `ALen a -> Printf.sprintf "%s!len" @@ to_z3_ident a
  | `AInd a -> Printf.sprintf "%s?ind" @@ to_z3_ident a
  | `AElem a -> Printf.sprintf "%s->$i" @@ to_z3_ident a
  | `AVar v -> v
  | `APre v -> Printf.sprintf "%s!old" v

let rec pre = function
  | `ADeref f -> `ADeref (pre f)
  | `AProj (d,i) -> `AProj (pre d,i)
  | `AVar v -> `APre v
  | `APre v -> `APre v

let t_ind a i = `AProj (a,i)

let rec is_const_ap = function
  | `APre _
  | `AVar _ -> true
  | `AProj (ap,_) -> is_const_ap ap
  | `ADeref _ -> false

let rec has_root v = function
  | `APre _ -> false
  | `AVar v' -> v = v'
  | `ADeref ap
  | `AProj (ap,_) -> has_root v ap

let rec has_root_p p = function
  | `AVar v -> p v
  | `APre _ -> false
  | `ADeref ap
  | `AProj (ap,_) -> has_root_p p ap

module PathSet = Set.Make(struct
    type t = concr_ap
    let compare = Stdlib.compare
  end)

open Sexplib.Std

type 'a _const_ap = [
  | `AVar of string
  | `ALen of 'a
  | `AProj of 'a * int
  | `APre of string
] [@@deriving sexp]

type const_ap = const_ap _const_ap [@@deriving sexp]

type 'a t_templ = [
  |  'a _const_ap
  | `ADeref of 'a
  | `AElem of 'a
  | `AInd of 'a
] [@@deriving sexp]


type concr_ap = [ | concr_ap t_templ ] [@@deriving sexp]

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
  | `AInd _
  | `AElem _
  | `ALen _ -> failwith "Not supported"

let t_ind a i = `AProj (a,i)

let rec is_pre : ([< 'b t_templ] as 'b) -> bool = function
  | `APre _ -> true
  | `AProj (ap,_)
  | `ADeref ap -> is_pre ap
  | _ -> false

let rec is_const_ap : ([< 'b t_templ] as 'b) -> bool = function
  | `APre _
  | `AVar _ -> true
  | `ALen ap
  | `AProj (ap,_) -> is_const_ap ap
  | `AInd _
  | `AElem _ -> false
  | `ADeref ap -> is_pre (ap :> 'b)

let rec has_root_p p = function
  | `AVar v -> p v
  | `APre _ -> false
  | `ALen ap
  | `AInd ap
  | `AElem ap
  | `ADeref ap
  | `AProj (ap,_) -> has_root_p p ap


let has_root v = has_root_p @@ (=) v

let rec compare =
  let constr_code : ([< 'b t_templ] as 'b) -> int = function
    | `APre _ -> 1
    | `AVar _ -> 2
    | `AProj _ -> 3
    | `ADeref _ -> 4
    | `AElem _ -> 5
    | `AInd _ -> 6
    | `ALen _ -> 7
  in
  fun (a : [< 'b t_templ]) (b: 'b) ->
    let code_cmp = (constr_code a) - (constr_code b) in
    if code_cmp <> 0 then
      code_cmp
    else
      match a,b with
      | `APre a_nm,`APre b_nm
      | `AVar a_nm,`AVar b_nm ->
        String.compare a_nm b_nm
      | `ADeref sub1,`ADeref sub2
      | `AElem sub1, `AElem sub2
      | `AInd sub1, `AInd sub2
      | `ALen sub1, `ALen sub2 ->
        compare (sub1 :> 'b) (sub2 :> 'b)
      | `AProj (sub1,ind1),`AProj (sub2,ind2) ->
        let cmp = compare (sub1 :> 'b) (sub2 :> 'b) in
        if cmp <> 0 then cmp else ind1 - ind2
      | _,_ -> assert false

let rec unsafe_get_root = function
  | `APre _ -> raise @@ Invalid_argument "not rooted in var"
  | `AVar v -> v
  | `AProj (ap,_)
  | `ADeref ap
  | `ALen ap
  | `AInd ap
  | `AElem ap -> unsafe_get_root ap

module PathSet = Set.Make(struct
    type t = concr_ap
    let compare = compare
  end)

module PathMap = Map.Make(struct
    type t = concr_ap
    let compare = Stdlib.compare
  end)

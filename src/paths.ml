open Sexplib.Std

type 'a _const_ap = [
  | `AVar of string
  | `ALen of 'a
  | `AProj of 'a * int
  | `APre of string
  | `AFree of string
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
  | `AFree v -> Printf.sprintf "%s?free" v

let rec pre = function
  | `ADeref f -> `ADeref (pre f)
  | `AProj (d,i) -> `AProj (pre d,i)
  | `AVar v -> `APre v
  | `APre v -> `APre v
  | `AInd _
  | `AElem _
  | `AFree _
  | `ALen _ -> failwith "Not supported"

let rec free = function
  | `ADeref f -> `ADeref (free f)
  | `AProj (d,i) -> `AProj (free d,i)
  | `AVar v -> `AFree v
  | `AFree v -> `AFree v
  | `AInd _
  | `AElem _
  | `ALen _ 
  | `APre _ -> failwith "Not supported"

let t_ind a i = `AProj (a,i)

let rec is_pre : ([< 'b t_templ] as 'b) -> bool = function
  | `APre _ -> true
  | `AProj (ap,_)
  | `ADeref ap -> is_pre ap
  | _ -> false

let rec is_const_ap : ([< 'b t_templ] as 'b) -> bool = function
  | `APre _
  | `AVar _ -> true
  | `AFree _ -> false
  | `ALen ap
  | `AProj (ap,_) -> is_const_ap ap
  | `AInd _
  | `AElem _ -> false
  | `ADeref ap -> is_pre (ap :> 'b)

let rec has_root_p p = function
  | `AVar v -> p v
  | `AFree _
  | `APre _ -> false
  | `ALen ap
  | `AInd ap
  | `AElem ap
  | `ADeref ap
  | `AProj (ap,_) -> has_root_p p ap


let has_root v = has_root_p @@ (=) v

let rec map_root (f: string -> string) = function
  | `AVar s -> `AVar (f s)
  | `APre s -> `APre (f s)
  | `AFree s -> `AFree s
  | `ALen ap -> `ALen (map_root f ap)
  | `AElem ap -> `AElem (map_root f ap)
  | `AInd ap -> `AElem (map_root f ap)
  | `AProj (ap,i) -> `AProj (map_root f ap,i)
  | `ADeref ap -> `ADeref (map_root f ap)

let rec is_array_path : ([< 'a t_templ] as 'a) -> bool = function
  | `ALen _
  | `AInd _
  | `AElem _ -> true
  | `ADeref ap
  | `AProj (ap,_) -> is_array_path ap
  | _ -> false

let rec compare =
  let constr_code : ([< 'b t_templ] as 'b) -> int = function
    | `APre _ -> 1
    | `AVar _ -> 2
    | `AFree _ -> 3
    | `AProj _ -> 4
    | `ADeref _ -> 5
    | `AElem _ -> 6
    | `AInd _ -> 7
    | `ALen _ -> 8
  in
  fun (a : [< 'b t_templ]) (b: 'b) ->
    let code_cmp = (constr_code a) - (constr_code b) in
    if code_cmp <> 0 then
      code_cmp
    else
      match a,b with
      | `APre a_nm,`APre b_nm
      | `AFree a_nm,`AFree b_nm
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
  | `AFree _
  | `APre _ -> raise @@ Invalid_argument "not rooted in var"
  | `AVar v -> v
  | `AProj (ap,_)
  | `ADeref ap
  | `ALen ap
  | `AInd ap
  | `AElem ap -> unsafe_get_root ap

let rec has_prefix (d: [< 'a t_templ] as 'a) (g: 'a) =
  if g = d then
    true
  else
    match g with
    | `ADeref ap
    | `AProj (ap,_)
    | `ALen ap
    | `AInd ap
    | `AElem ap -> has_prefix d ap
    | `AVar _
    | `AFree _
    | `APre _ -> false

module PathSet = Set.Make(struct
    type t = concr_ap
    let compare = compare
  end)

module PathMap = Map.Make(struct
    type t = concr_ap
    let compare = Stdlib.compare
  end)

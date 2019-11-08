open Sexplib.Std

type root = [
  (* name, pre, null? *)
  | `AVar of string * bool * bool
  | `ARet of bool
] [@@deriving sexp]

type 'a _const_ap = [
  | root
  | `ALen of 'a
  | `AProj of 'a * int
] [@@deriving sexp]

type const_ap = const_ap _const_ap [@@deriving sexp]

type 'a t_templ = [
  |  'a _const_ap
  | `ADeref of 'a
  | `AElem of 'a
  | `AInd of 'a
] [@@deriving sexp]


type concr_ap = [ | concr_ap t_templ ] [@@deriving sexp]

let null_suff b s = if b then s ^ "?null" else s

let rec to_z3_ident = function
  | `ADeref d -> Printf.sprintf "%s->*" @@ to_z3_ident d
  | `AProj (a,i) -> Printf.sprintf "%s->%d" (to_z3_ident a) i
  | `ALen a -> Printf.sprintf "%s!len" @@ to_z3_ident a
  | `AInd a -> Printf.sprintf "%s?ind" @@ to_z3_ident a
  | `AElem a -> Printf.sprintf "%s->$i" @@ to_z3_ident a
  | `AVar (v,pre,null) ->
    let base = if pre then v ^ "!old" else v in
    null_suff null base
  | `ARet null -> null_suff null "$ret"

let rec pre = function
  | `ADeref f -> `ADeref (pre f)
  | `AProj (d,i) -> `AProj (pre d,i)
  | `ALen p -> `ALen (pre p)
  | `AVar (v,f,_)-> `AVar (v,f,true)

  | `ARet _
  | `AInd _
  | `AElem _ -> failwith "Not supported"

let t_ind a i = `AProj (a,i)
let elem p = `AElem p
let deref p = `ADeref p
let len p = `ALen p
let var v = `AVar (v,false,false)
let arg_name = Printf.sprintf "$%d"
let arg i = var @@ arg_name i
let ind i = `AInd i
let ret = `ARet false
      
let rec is_pre : ([< 'b t_templ] as 'b) -> bool = function
  | `AVar (_,d,_) -> d
  | `AProj (ap,_)
  | `ADeref ap -> is_pre ap
  | _ -> false

let rec is_const_ap : ([< 'b t_templ] as 'b) -> bool = function
  | `AVar _ -> true
  | `ARet _ -> false
  | `ALen ap
  | `AProj (ap,_) -> is_const_ap ap
  | `AInd _
  | `AElem _ -> false
  | `ADeref ap -> is_pre (ap :> 'b)

let rec has_root_p p = function
  | `AVar (v,_,_) -> p v
  | `ARet _ -> false
  | `ALen ap
  | `AInd ap
  | `AElem ap
  | `ADeref ap
  | `AProj (ap,_) -> has_root_p p ap


let has_root v = has_root_p @@ (=) v

let rec map_root (f: string -> string) = function
  | `AVar (s,p,n) -> `AVar ((f s),p,n)
  | `ARet n -> `ARet n
  | `ALen ap -> `ALen (map_root f ap)
  | `AElem ap -> `AElem (map_root f ap)
  | `AInd ap -> `AInd (map_root f ap)
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
    | `ARet _ -> 0
    | `AVar _ -> 2
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
      | `AVar (a_nm,p1,n1),`AVar (b_nm,p2,n2) ->
        Stdlib.compare (p1,n1,a_nm) (p2,n2,b_nm)
      | `ADeref sub1,`ADeref sub2
      | `AElem sub1, `AElem sub2
      | `AInd sub1, `AInd sub2
      | `ALen sub1, `ALen sub2 ->
        compare (sub1 :> 'b) (sub2 :> 'b)
      | `AProj (sub1,ind1),`AProj (sub2,ind2) ->
        let cmp = compare (sub1 :> 'b) (sub2 :> 'b) in
        if cmp <> 0 then cmp else ind1 - ind2
      | `ARet b1,`ARet b2 -> Bool.compare b1 b2
      | _,_ -> assert false

let rec unsafe_get_root = function
  | `ARet _ -> assert false
  | `AVar (v,_,_) -> v
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
    | `ARet _ -> false


module PathOrd = struct
  type t = concr_ap
  let compare = compare
end

module PathSet = Set.Make(PathOrd)
module PathMap = Map.Make(PathOrd)

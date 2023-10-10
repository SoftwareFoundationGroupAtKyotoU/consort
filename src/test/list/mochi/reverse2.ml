let rec mklist n =
  if n > 0 then
    let h = Random.int 0 in
    let t = mklist (n - 1) in
    h :: t
  else []

and _reverse (l: int list) (acc: int list) =
  match l with
    [] -> acc
  | h :: t -> _reverse t (h :: acc)

and reverse (l: int list) =
  _reverse l []

and len (l: int list) =
  match l with
    [] -> 0
  | _ :: t -> 1 + len t

let main () =
  let n =
    let rec nd' () =
      let _' = Random.int 0 in
      if _' >= 0 then _' else nd' ()
    in nd' ()
  in
  let l = mklist n in
  let __t0 = len l in
  let rev_l = reverse l in
  let __t1 = len rev_l in
  assert (__t0 = __t1);
  let __t2 = 0 in
  (())

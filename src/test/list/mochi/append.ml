let rec mklist n =
  if n > 0 then
    let h = Random.int 0 in
    let t = mklist (n - 1) in
    h :: t
  else []

and len (l: int list) =
  match l with
    [] -> 0
  | _ :: t -> 1 + len t

and append (l1: int list) (l2: int list) =
  match l1 with
    [] -> l2
  | h :: t -> h :: (append t l2)

let main () =
  let m =
    let rec nd' () =
      let _' = Random.int 0 in
      if _' >= 0 then _' else nd' ()
    in nd' ()
  in
  let n =
    let rec nd' () =
      let _' = Random.int 0 in
      if _' >= 0 then _' else nd' ()
    in nd' ()
  in
  let l1 = mklist m in
  let l2 = mklist n in
  let sum_length = len l1 + len l2 in
  let l = append l1 l2 in
  assert (len(l) = sum_length);
  (())

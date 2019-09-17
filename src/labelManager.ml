let counter = ref 0;;

let _internal_fresh () =
  let to_ret = !counter in
  incr counter;
  to_ret

let register pos =
  let to_ret = _internal_fresh () in
  to_ret,pos

let register_with (_,pos) =
  let to_ret = _internal_fresh () in
  (to_ret,pos)

let _internal_incr i =
  if i > !counter then
    counter := (i + 1)
    

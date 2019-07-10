let counter = ref 0;;

let tracker = Hashtbl.create 10;;

let register ?ctxt () =
  let to_ret = !counter in
  incr counter;
  match ctxt with
  | None -> to_ret
  | Some c_label ->
    Hashtbl.add tracker to_ret c_label; to_ret

let get_label_expl () =
  Hashtbl.fold (fun k v accum -> (k,v)::accum) tracker []
   
let print_label_explanation () =
  Hashtbl.iter (Printf.printf "Label %d is from desugaring of: %d\n") tracker

let _internal_incr i =
  if i > !counter then
    counter := (i + 1)
    

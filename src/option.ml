let map f = function
  | Some x -> Some (f x)
  | None -> None

let iter f = function
  | Some x -> f x
  | None -> ()

let value o ~default = match o with
  | Some o -> o
  | None -> default

open Sexplib.Std
include Map.Make(String)

let t_of_sexp (type v_type) ~(v: Sexplib.Sexp.t -> v_type)  sexp =
  let v_type_of_sexp = v in
  [%of_sexp: (string * v_type) list] sexp
  |> List.fold_left (fun acc (k,v) ->
      add k v acc) empty

let sexp_of_t (type v_type) ~(v: v_type -> Sexplib.Sexp.t) t =
  let sexp_of_v_type = v in
  bindings t
  |> [%sexp_of: (string * v_type) list]

let of_bindings l = List.fold_left (fun acc (k,v) ->
    add k v acc
  ) empty l

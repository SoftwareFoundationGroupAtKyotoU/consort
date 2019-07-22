module Option = struct
  let map f = function
    | Some x -> Some (f x)
    | None -> None

  let iter f = function
    | Some x -> f x
    | None -> ()

  let value o ~default = match o with
    | Some o -> o
    | None -> default

  (* I understand monads *)
  let bind f = function
    | Some x -> f x
    | None -> None

  let return x = Some x
end

module IntMap = Map.Make(struct
    type t = int
    let compare n1 n2 = n1 - n2
  end)

module StringSet = Set.Make(String)

module CoHypS = Set.Make(struct
    type t = int * int
    let compare (a1,b1) (a2,b2) =
      let a_cmp = a1 - a2 in
      if a_cmp = 0 then b1 - b2 else a_cmp
  end)

let double_fold_k f l k =
  List.fold_left (fun acc t ->
    (fun d1 d2 ->
      f d1 d2 t (fun d1' d2' ->
        acc d1' d2'
      )
    )
  ) k l

let double_fold f l =
  List.fold_left (fun acc t ->
    (fun d1 d2 ->
      let (d1',d2') = f d1 d2 t in
      acc d1' d2'
    )
  ) (fun d1_final d2_final -> (d1_final, d2_final)) l

let map_with_accum acc f l =
  double_fold (fun acc' tl e ->
    let (acc'',e') = f acc' e in
    (acc'',e'::tl)
  ) l acc []

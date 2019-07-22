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

module IntMap = Map.Make(Int)
module IntSet = Set.Make(Int)
module StringSet = Set.Make(String)

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

let map_with_accum f l acc =
  double_fold (fun acc' tl e ->
    let (acc'',e') = f e acc' in
    (acc'',e'::tl)
  ) l acc []

let fold_left_fst f = function
  | [] -> None
  | h::l -> Option.some @@ List.fold_left f h l

module StateMonad = struct
  module Let_syntax = struct
    type ('a,'b,'c) context_monad = ('b -> ('c * 'a))

    let bind (o: ('a,'b,'c) context_monad) ~f =
      (fun ctxt ->
        let (c',a) = o ctxt in
        f a c')

    let map (o: ('a,'b,'c) context_monad) ~f =
      (fun ctxt ->
        let (c',a) = o ctxt in
        (c',f a))

    let both a b =
      (fun ctxt ->
        let (c1,a_res) = a ctxt in
        let (c2,b_res) = b c1 in
        (c2,(a_res,b_res)))

    let return g = (fun ctxt -> (ctxt,g))

    let mwith o ~(f : ('d -> ('a,'b,'c) context_monad)) : ('a,'b,'c) context_monad = (fun ctxt ->
      let v = o ctxt in
      f v ctxt)
  end

  let return = Let_syntax.return

  let return_mut ctxt = (ctxt,())

  (* combinators *)

  (* pipelining. Take monad a producing a value r and state s,
     and return a monad producing value r and state (b s) *)
  let (<|>) a b = fun ctxt ->
    let (c',r) = a ctxt in
    let c'' = b c' in
    (c'',r)

  (* sequencing and the dual of the above.
     Produce a computation that transforms the state according to d1
     and then produces a state and value according to d2 in the new state *)
  let (>>) d1 d2 = (fun ctxt -> let c = d1 ctxt in d2 c)

  (* sugar *)
  let map_state f ctxt = f ctxt

  (* reify the state *)
  let get_state = fun ctxt -> ((),ctxt)

  (* sets the state *)
  let put_state ctxt () = (ctxt,())

  (* exactly the same as return, but designed for us with the pipelining *)
  let return_after b = (fun ctxt ->
    (ctxt,b)
  )

  (* produce a value from the current state according to f *)
  let mwith f ctxt = ctxt,(f ctxt)

  (* placeholder "argument" for stateful computations who take the state
     as the second to last argument *)
  let (@>) f a = (fun ctxt -> f ctxt a)
  (* run a computation f in state c, expecting the computation to return (). Return
     the new state *)
  let do_with_context c f = let (c',()) = (f c) in c'
  (* produces a computation that mutates the state and generates no side effect *)
  let mutate f ctxt = let ctxt' = f ctxt in (ctxt',())

  (* generate the unit value *)
  let and_done ctxt = (ctxt,())

  (* stateful versions of list functions *)
  let mfold_left f a l = List.fold_left (fun a e ->
      let%bind a' = a in
      f a' e
    ) (return a) l

  let mfold_right f l a = List.fold_right (fun e a ->
      let%bind a' = a in
      f e a'
    ) l (return a)

  let mfold_left2 f a l1 l2 =
    List.fold_left2 (fun a e1 e2 ->
      let%bind a_raw = a in
      f a_raw e1 e2
    ) (return a) l1 l2


  let mfold_right2 f l1 l2 a =
    List.fold_right2 (fun e1 e2 a ->
      let%bind a_raw = a in
      f e1 e2 a_raw
    ) l1 l2 (return a)

end

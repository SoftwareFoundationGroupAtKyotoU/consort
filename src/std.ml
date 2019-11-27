module type PRINTABLE = sig
  type t
  val to_string : t -> string
end

module type PRINTSET = sig
  include Set.S
  include PRINTABLE with type t := t
end

module PrintSet(P: sig
      include Set.OrderedType
      include PRINTABLE with type t := t
    end) : PRINTSET with type elt = P.t = struct
  include Set.Make(P)
  let to_string e = elements e |> List.map P.to_string |> String.concat ", " |> Printf.sprintf "{%s}"
end

module IntMap = Map.Make(Int)
module IntSet = PrintSet(Int)
module StringSet = PrintSet(struct include String let to_string = Fun.id end)

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

let fold_lefti f a l =
  let rec loop i a l =
    match l with
    | [] -> a
    | h::t -> loop (i+1) (f i a h) t
  in
  loop 0 a l

let fold_left2i f a l1 l2 =
  let rec loop i a l1 l2 =
    match l1,l2 with
    | h1::t1,h2::t2 ->
      loop (i+1) (f i a h1 h2) t1 t2
    | [],[] -> a
    | _,_ -> raise @@ Invalid_argument "unequal lengths"
  in
  loop 0 a l1 l2
    
let fold_left3i f a l1 l2 l3 =
  let rec inner_loop i acc l1 l2 l3 =
    match l1,l2,l3 with
    | h1::t1,h2::t2,h3::t3 ->
      inner_loop (i+1) (f acc i h1 h2 h3) t1 t2 t3
    | [],[],[] -> acc
    | _ -> raise @@ Invalid_argument "differing lengths"
  in
  inner_loop 0 a l1 l2 l3

let rec update_nth l i v =
  match l with
  | h::t ->
    if i = 0 then
      v::t
    else
      h::(update_nth t (i - 1) v)
  | [] -> raise @@ Invalid_argument "Bad index"

module IntExt = struct
  let rec fold f acc i =
    if i < 0 then
      raise @@ Invalid_argument "negative fold"
    else if i = 0 then acc
    else fold f (f acc) (i - 1)
end

module StringExt = struct
  let starts_with s pref =
    if String.length s < String.length pref then
      false
    else
      (String.sub s 0 (String.length pref)) = pref
end

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

    let seq ~a ~b =
      (fun ctxt ->
        let (ctxt',()) = a ctxt in
        b ctxt')

    let proj ~f ctxt =
      let v = f ctxt in
      (ctxt,v)

    let mut ~f ctxt =
      let ctxt' = f ctxt in
      (ctxt',())
  end

  let return = Let_syntax.return

  (* combinators *)

  (* sequencing and the dual of the above.
     Produce a computation that transforms the state according to d1
     and then produces a state and value according to d2 in the new state *)
  let (>>) d1 d2 = (fun ctxt -> let (c,()) = d1 ctxt in d2 c)

  (* sugar *)
  let map_state f ctxt = (f ctxt,())

  (* reify the state *)
  let get_state = fun ctxt -> ((),ctxt)

  (* sets the state *)
  let put_state ctxt () = (ctxt,())

  (* produce a value from the current state according to f *)
  let mwith f = Let_syntax.proj ~f

  (* run a computation f in state c, expecting the computation to return (). Return
     the new state *)
  let do_with_context c f = let (c',()) = (f c) in c'
  (* produces a computation that mutates the state and generates no side effect *)
  let mutate f = Let_syntax.mut ~f

  (* stateful versions of list functions *)
  let mfold_left f a l = List.fold_left (fun a e ->
      let%bind a' = a in
      f a' e
    ) (return a) l

  let rec mmap f l =
    match l with
    | [] -> return []
    | h::t ->
      let%bind h' = f h in
      let%bind t' = mmap f t in
      return @@ h'::t'

  let mmapi f l =
    let rec loop i l =
      match l with
      | [] -> return []
      | h::t ->
        let%bind h' = f i h in
        let%bind t' = loop (i+1) t in
        return @@ h'::t'
    in
    loop 0 l

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

  let rec miter f l =
    match l with
    | [] -> return ()
    | h::t ->
      let%bind () = f h in
      miter f t

  let miteri f =
    let rec loop i = function
      | [] -> return ()
      | h::t ->
        let%bind () = f i h in loop (i + 1) t
    in
    loop 0

end

module ListMonad = struct
  let return a = [a]

  let bindi f l = fold_lefti (fun i a e ->
      (f i e)@a
    ) [] l
      
  let bind f l = bindi (fun _ e -> f e) l
end

module DefaultOrd(O: sig type t end) = struct
  type t = O.t
  let compare : t -> t -> int = Stdlib.compare
end

module OrderedPair(O1: Map.OrderedType)(O2: Map.OrderedType) : Map.OrderedType with type t = O1.t * O2.t = struct
  type t = O1.t * O2.t

  let compare (a1,a2) (b1,b2) =
    let c1 = O1.compare a1 b1 in
    if c1 = 0 then
      O2.compare a2 b2
    else
      c1
end

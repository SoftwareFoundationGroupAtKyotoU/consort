(** Our custom standard library *)

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

module IntMap = struct
  open Sexplib.Std
  include Map.Make(Int)
  let sexp_of_t (type v_type) ~(v: v_type -> Sexplib.Sexp.t) t =
    let sexp_of_v_type = v in
    bindings t
    |> [%sexp_of: (int * v_type) list]
end

module IntSet = PrintSet(Int)
module StringSet = PrintSet(struct include String let to_string = Fun.id end)

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

(** A state monad. The Let_syntax module is for use with the ppx_let
   processor (we could in principle use the new binding extension in
   4.08, but we're in too deep now!)

   The state monad itself is given a fairly standard definition
   (although note the type of state may be changed by a
   computation). Two convenience functions, [proj] and [mut] are used
   to lift functions that operate on the state directly. [proj] lifts a
   function that "projects" some information out of the state (i.e., of type [state -> 'a])
   into a monadic operation that can be sequenced with >>=. [mut] lifts
   a function that mutates the state (e.g., of type [state -> state]) and lifts
   it into monadic operation that can be sequenced with >> or seq. 

   The convenience function, [seq] composes two monadic operations, where the first operation
   is assumed to side effect the state (and therefore produces [()]).

   These three convenience functions are rarely (if ever?) used directly, they are used
   by the [with_monad] ppx extension. The extension [lq] (for "lift query", the mnemonic should be lift projection...)
   function definition let-bindings is desugared into a call to proj, and the extension [lm] (for lift mutation)
   on a function definition let-binding is similarly desugared into a call to mut. Finally, to simulate do blocks, the
   [m] extension on begin o1; o2; o3; .. end is desguared into a sequence of [seq] calls.
*)

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
  let (>>) d1 d2 = (fun ctxt -> let (c,()) = d1 ctxt in d2 c)

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


module OptionMonad = struct
  let (let*) o f =
    match o with
    | None -> None
    | Some s -> f s
end

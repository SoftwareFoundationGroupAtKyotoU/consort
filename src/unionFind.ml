module type UF = sig
  type t
  type key
  val find: t -> key -> key
  val maybe_find : t -> key -> key
  val union: t -> key -> key -> unit
  val mk: unit -> t
end

module InternalMake(K : sig
      type key
      val hash : key -> int
      val equal : key -> key -> bool
      type state
      val init : state
      val weight : key -> int
    end) = struct
  type node = {
    id : K.key;
    mutable parent: node;
    mutable rank: int
  }

  module KeyHash = Hashtbl.Make(
      struct
        type t = K.key
        include K
    end)

  type t = {
    table: node KeyHash.t;
    mutable state: K.state;
  }

  let mk () =
    {
      table = KeyHash.create 10;
      state = K.init
    }

  let make_and_add uf k =
    let rec node = { id = k; parent = node; rank = 1 } in
    KeyHash.add uf.table k node

  let rec compress node =
    if node.parent == node then
      node
    else
      let found = compress node.parent in
      node.parent <- found;
      found

  let find_internal uf id1 =
    let node = KeyHash.find uf.table id1 in
    (compress node)

  let find uf id1 =
    (find_internal uf id1).id

  let maybe_find uf id1 =
    if KeyHash.mem uf.table id1 then
      find uf id1
    else
      id1

  let union uf id1 id2 =
    let n1 = find_internal uf id1 in
    let n2 = find_internal uf id2 in
    if n1 == n2 then
      ()
    else begin
      if n2.rank < n1.rank then
        n2.parent <- n1
      else if n1.rank < n2.rank then
        n1.parent <- n2
      else
        let w1 = K.weight id1 in
        let w2 = K.weight id2 in
        let (new_root,child) =
          if w1 < w2 then
            (n1,n2)
          else
            (n2,n1)
        in
        child.parent <- new_root;
        new_root.rank <- new_root.rank + 1
    end
end


module type UnionKey = sig
  type t
  val hash : t -> int
  val equal : t -> t -> bool
  val weight : t -> int
end

module Make(K : UnionKey) = struct
  include InternalMake(struct
      type key = K.t
      let hash = K.hash
      let equal = K.equal
      let weight = K.weight
      type state = unit
      let init = ()
    end)

  let register uf k =
    if KeyHash.mem uf.table k then
      ()
    else
      make_and_add uf k
end

include InternalMake(struct
    type key = int
    let hash i = i
    let equal = (=)
    type state = int
    let init = 0
    let weight i = i
  end)

let new_node uf =
  let id = uf.state in
  make_and_add uf id;
  uf.state <- id + 1; id

module MakeHashed(K : sig
      type t
      val equal : t -> t -> bool
    end) = struct
  include K
  let weight _ = 0
  let hash = Hashtbl.hash
end

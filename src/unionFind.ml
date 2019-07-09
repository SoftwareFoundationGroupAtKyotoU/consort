module type UF = sig
  type t
  type key
  val find: t -> key -> key
  val union: t -> key -> key -> unit
  val mk: (parent:key -> child:key -> unit) -> t
end

type node = {
  id: int;
  mutable parent: node;
  mutable rank: int;
}

type t = {
  table: (int, node) Hashtbl.t;
  mutable next: int;
  merge_hook : parent:int -> child:int -> unit
}

let make_and_add uf =
  let rec node = { id = uf.next; parent = node; rank = 1 } in
  Hashtbl.add uf.table node.id node;
  uf.next <- uf.next + 1;
  node.id

let mk merge_hook =
  let uf = { table = Hashtbl.create 10; next = 0; merge_hook } in
  (*List.iter (fun r ->
     Some r |> (make_and_add uf) |> ignore
     ) roots;*)
  uf

let rec compress node =
  if node.parent == node then
    node
  else
    let found = compress node.parent in
    node.parent <- found;
    found

let find_internal uf id1 =
  let node = Hashtbl.find uf.table id1 in
  (compress node)

let find uf id1 =
  (find_internal uf id1).id

let union uf id1 id2 =
  let n1 = find_internal uf id1 in
  let n2 = find_internal uf id2 in
  if n1 == n2 then
    ()
  else begin
    let (new_root,child) = begin
      if n2.rank < n1.rank then
        (n2.parent <- n1; (n1,n2))
      else if n1.rank < n2.rank then
        (n1.parent <- n2; (n2,n1))
      else
        (let (new_root,child) = (n1,n2) in
        child.parent <- new_root;
        new_root.rank <- new_root.rank + 1;
        (new_root,child))
    end in
    uf.merge_hook ~parent:new_root.id ~child:child.id
  end

let new_node uf = make_and_add uf

module Make(K : sig
      type key
      val hash : key -> int
      val compare : key -> key -> int
    end) = struct

  module KeyHash = Hashtbl.Make(struct
      type t = K.key
      let hash = K.hash
      let equal i j = (K.compare i j) = 0
    end)

  type _t = {
    uf: t;
    rev_mapping: (int,K.key) Hashtbl.t;
    key_mapping: int KeyHash.t
  }

  let mk cb = 
    let rev_mapping = Hashtbl.create 10 in
    let key_mapping = KeyHash.create 10 in
    {
      uf = mk (fun ~parent ~child ->
          cb
            ~parent:(Hashtbl.find rev_mapping parent)
            ~child:(Hashtbl.find rev_mapping child));
      rev_mapping; key_mapping
    }

  let find { uf; key_mapping; rev_mapping } k =
    let k_id = KeyHash.find key_mapping k in
    Hashtbl.find rev_mapping (find uf k_id)

  let union { uf; key_mapping; _ } k1 k2 =
    union uf
      (KeyHash.find key_mapping k1)
      (KeyHash.find key_mapping k2)

  let register { uf; key_mapping; rev_mapping } k =
    if KeyHash.mem key_mapping k then
      ()
    else
      let id = new_node uf in
      KeyHash.add key_mapping k id;
      Hashtbl.add rev_mapping id k

  type t = _t
end

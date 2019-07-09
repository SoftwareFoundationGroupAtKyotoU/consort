module type UF = sig
  type t
  type key
  val find: t -> key -> key
  val union: t -> key -> key -> unit
  val mk: (parent:key -> child:key -> unit) -> t
end

type t
include UF with type key := int and type t := t
val new_node: t -> int

module Make(K : sig
      type key
      val hash : key -> int
      val compare : key -> key -> int
    end) : sig
  type t
  include UF with type key := K.key and type t := t
  val register : t -> K.key -> unit
end

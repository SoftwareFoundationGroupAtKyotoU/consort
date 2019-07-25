module type UF = sig
  type t
  type key
  val find: t -> key -> key
  val union: t -> key -> key -> unit
  val mk: unit -> t
end

type t
include UF with type key := int and type t := t
val new_node: t -> int

module Make(K : sig
      type t
      val hash : t -> int
      val equal : t -> t -> bool
    end) : sig
  type t
  include UF with type key := K.t and type t := t
  val register : t -> K.t -> unit
end

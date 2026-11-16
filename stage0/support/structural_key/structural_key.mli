module Make (Key : sig
  type t
end) : sig
  type t = Key.t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

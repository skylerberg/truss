module type Node = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

module Make (Node : Node) : sig
  val of_graph : successors:(Node.t -> Node.t list) -> Node.t list -> Node.t list list
end

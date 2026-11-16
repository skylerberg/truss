module type Node = sig
  type t

  val equal : t -> t -> bool
  val hash : t -> int
  val compare : t -> t -> int
end

val find_components :
  (module Node with type t = 'node) ->
  successors:('node -> 'node list) ->
  'node list ->
  'node list list

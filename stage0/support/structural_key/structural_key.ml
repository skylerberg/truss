module Make (Key : sig
  type t
end) =
struct
  type t = Key.t

  let equal : t -> t -> bool = ( = )
  let hash : t -> int = Hashtbl.hash_param 64 256
  let compare : t -> t -> int = Stdlib.compare
end

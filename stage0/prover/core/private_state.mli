type t
type 'state key

val create : unit -> t
val make_key : (unit -> 'state) -> 'state key
val read : t -> 'state key -> 'state

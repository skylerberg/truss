type t = { enabled : bool; mutable drawn : bool }

val create : enabled:bool -> t
val show : t -> string -> unit
val clear : t -> unit

module For_testing : sig
  val cut : string -> int -> string
end

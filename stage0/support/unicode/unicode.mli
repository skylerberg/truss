val version : string

module Decoded : sig
  type t [@@immediate]

  val is_valid : t -> bool
  val code_point : t -> int
  val length : t -> int
end

val decode : string -> int -> Decoded.t
val encode : Buffer.t -> int -> unit
val of_code_points : int list -> string
val is_xid_start : int -> bool
val is_xid_continue : int -> bool
val is_forbidden : int -> bool
val is_bidi_control : int -> bool
val is_control : int -> bool
val find_forbidden_name : int -> string option

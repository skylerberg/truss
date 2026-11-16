val derive_key : context:string -> string -> string
val to_hex : string -> string
val hex_digest : ?digits:int -> string -> string

module For_testing : sig
  val hash : string -> string
end

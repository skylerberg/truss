val derive_key : context:string -> string -> string
val to_hex : string -> string
val hash_to_hex : ?digits:int -> string -> string

module For_testing : sig
  val hash : string -> string
end

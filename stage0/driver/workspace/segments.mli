type t

val open_ : string -> (t, [ `Open_elsewhere ]) result
val header : t -> string list option
val read_entries : t -> (string * string) list option
val commit : t -> header:string list -> (string * string option) list -> unit
val discard : t -> unit
val close : t -> unit

module For_testing : sig
  val interrupted_commit : t -> header:string list -> (string * string option) list -> unit
end

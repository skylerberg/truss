type t

val open_ : string -> stop_holder:(unit -> bool) -> (t, [ `Open_elsewhere ]) result
val header : t -> string option
val read_entries : t -> (string * string) list option
val commit : t -> header:string -> (string * string option) list -> unit
val discard : t -> unit
val close : t -> unit

module For_testing : sig
  val interrupt_commit : t -> header:string -> (string * string option) list -> unit
end

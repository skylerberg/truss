type t = {
  out : string -> unit;
  err : string -> unit;
  terminal : bool;
  columns : int option;
  mutable json : bool;
}

val with_ : t -> (unit -> 'a) -> 'a
val print : string -> unit
val print_line : string -> unit
val printf : ('a, unit, string, unit) format4 -> 'a
val eprint : string -> unit
val eprint_line : string -> unit
val eprintf : ('a, unit, string, unit) format4 -> 'a
val terminal : unit -> bool
val columns : unit -> int option
val json : unit -> bool
val set_json : bool -> unit

type outcome = Passed | Failed | Panicked | Incomplete | Timed_out | Crashed

val show_outcome : outcome -> string

type record = {
  outcome : outcome;
  message : string option;
  echo : string option;
  output : string option;
  microseconds : int;
  cached : bool;
}

exception Malformed of string

type reader

val make_reader : tests:int -> ?on_start:(int -> unit) -> (int -> record -> unit) -> reader
val feed : reader -> string -> unit

module For_testing : sig
  val parse : tests:int -> string -> (record list, string) result
  val list_records_by_piece : tests:int -> string list -> (int * record) list
end

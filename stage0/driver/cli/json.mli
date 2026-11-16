type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | List of t list
  | Object of (string * t) list
  | Raw of string

val to_string : t -> string
val encode_option : ('a -> t) -> 'a option -> t
val make_document : diagnostics:t list -> (string * t) list -> t
val print : t -> unit

exception Malformed

val parse : string -> t
val lookup_field : string -> t -> t

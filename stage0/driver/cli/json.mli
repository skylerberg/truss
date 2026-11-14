type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | List of t list
  | Object of (string * t) list
  | Raw of string

val to_string : t -> string
val option : ('a -> t) -> 'a option -> t
val document : diagnostics:t list -> (string * t) list -> t
val print : t -> unit

exception Malformed

val parse : string -> t
val field : string -> t -> t

type t =
  | Integer of Z.t
  | Bytes of string
  | Text of string
  | Array of t list
  | Map of (t * t) list
  | Tag of int * t
  | Bool of bool
  | Null
  | Float of float

val int : int -> t
val encode : t -> string

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
val decode : string -> t option
val find_int : t -> int option
val find_list : (t -> 'a option) -> t -> 'a list option

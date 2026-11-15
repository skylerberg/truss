type entry = { name : Path.package; version : Version.t; hash : string; holds : string list }
type t = entry list

exception Malformed of { line : int; message : string }

val parse : string -> t
val print : t -> string
val find : t -> Path.package -> entry option

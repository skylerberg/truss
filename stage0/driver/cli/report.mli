type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Database.session -> Path.package list -> t
val of_files : file list -> t
val clean : t -> bool
val document : t -> (string * Json.t) list -> Json.t
val plural : int -> string -> string -> string
val print : t -> unit

exception Errors of t

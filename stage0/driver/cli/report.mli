type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Pipeline.t -> Database.snapshot -> Path.package list -> t
val of_files : file list -> t
val proofs : t -> Proofs.t option
val clean : t -> bool
val document : t -> (string * Json.t) list -> Json.t
val plural : int -> string -> string -> string
val print : t -> unit

exception Errors of t

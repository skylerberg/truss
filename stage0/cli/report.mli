type file = { module_ : Path.module_; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Project.t -> t
val of_files : file list -> t
val clean : t -> bool
val document : t -> (string * Json.t) list -> Json.t
val plural : int -> string -> string -> string
val print : t -> unit

type file = { module_ : Path.module_; source : Source.t; diagnostics : Diagnostic.t list }
type t = { checked : file list; proven : file list Lazy.t; problems : string list }

val gather : ?proofs:bool -> Project.t -> t
val of_files : file list -> t
val files : t -> file list
val clean : t -> bool
val document : t -> (string * Json.t) list -> Json.t
val plural : int -> string -> string -> string
val print : t -> unit

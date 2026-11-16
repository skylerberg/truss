type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Database.t -> Workspace.snapshot -> Path.package list -> t
val of_files : file list -> t
val force_proofs : t -> Proofs.t option
val clean : t -> bool
val make_document : t -> (string * Json.t) list -> Json.t
val pluralize : int -> string -> string -> string
val print : t -> unit

exception Errors of t

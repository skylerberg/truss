type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Database.t -> Workspace.snapshot -> Path.package list -> t
val of_files : file list -> t
val force_proofs : t -> Proofs.t option
val has_errors : t -> bool
val make_document : t -> (string * Json.t) list -> Json.t
val print : ?offers_fix:bool -> t -> unit

exception Errors of t

val require_no_errors : t -> unit

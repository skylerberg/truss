type file = { file : Path.file; source : Source.t; diagnostics : Diagnostic.t list }
type t

val gather : ?proofs:bool -> Project.t -> t
val of_files : file list -> t
val clean : t -> bool
val document : t -> (string * Json.t) list -> Json.t
val plural : int -> string -> string -> string
val print : t -> unit
val refuse : json:bool -> ?fields:(string * Json.t) list -> t -> string list -> unit
val refused : json:bool -> ?fields:(string * Json.t) list -> ?reasons:string list -> t -> bool

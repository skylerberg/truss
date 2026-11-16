val render_signature :
  Resolve.Names.lookups -> body:bool -> opaque:bool -> Resolve.Names.key -> string

val show_kind : Resolve.Names.kind -> string
val find_signature : Resolve.Names.lookups -> Path.t -> string option
val label_signature : string -> string -> string
val is_signature : Database.Part.t -> bool

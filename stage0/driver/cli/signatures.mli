val render_signature :
  Resolve.Names.lookups ->
  Resolve.Names.source ->
  body:bool ->
  opaque:bool ->
  Resolve.Names.key ->
  string

val show_kind : Resolve.Names.kind -> string
val find_signature : Resolve.Names.lookups -> Resolve.Names.source -> Path.t -> string option
val label_signature : string -> string -> string

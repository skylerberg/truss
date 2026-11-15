val text : Resolve.Names.lookups -> body:bool -> opaque:bool -> Resolve.Names.key -> string option
val kind_word : Resolve.Names.kind -> string
val of_path : Resolve.Names.lookups -> Path.t -> string option
val labeled : string -> string -> string
val is_signature : Pipeline.Part.t -> bool

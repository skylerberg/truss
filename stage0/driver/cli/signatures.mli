val text : Query.context -> body:bool -> opaque:bool -> Resolve.Names.key -> string option
val kind_word : Resolve.Names.kind -> string
val parts : Query.part list
val of_path : Query.context -> Path.t -> string option
val labeled : string -> string -> string

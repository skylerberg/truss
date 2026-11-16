val path : Syntax.path -> string
val statement : Syntax.statement -> string
val definition : ?methods:string list -> Syntax.definition -> string
val definitions : Syntax.top_level list -> string list
val file : Syntax.file -> string

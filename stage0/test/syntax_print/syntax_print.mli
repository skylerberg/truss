val show_path : Syntax.path -> string
val show_statement : Syntax.statement -> string
val show_definition : ?methods:string list -> Syntax.definition -> string
val show_definitions : Syntax.top_level list -> string list
val show_file : Syntax.file -> string

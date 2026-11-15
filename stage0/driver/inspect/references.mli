type target = Definition of Path.t | Module of Path.module_
type occurrence = { span : Syntax.span; target : target }

val declared_name : Syntax.definition -> Syntax.name option
val occurrences : (Resolve.Names.key, occurrence list) Query.query
val uses : (Path.file, (Path.module_ * Source.span) list) Query.query
val names_definition : Path.t -> target -> bool

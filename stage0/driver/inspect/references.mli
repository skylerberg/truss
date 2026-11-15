type target = Definition of Path.t | Module of Path.module_
type occurrence = { span : Source.Definition_span.t; target : target }

val declared_name : Syntax.definition -> Syntax.name option

val occurrences :
  path:Path.t -> Syntax.definition -> Resolve.resolved -> Infer.tables option -> occurrence list

val uses :
  used_module:(Syntax.path -> Path.module_) ->
  Syntax.path Syntax.item list ->
  (Path.module_ * Source.span) list

val names_definition : Path.t -> target -> bool

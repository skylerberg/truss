type target =
  | Definition of Path.t
  | Module of { module_ : Path.module_; imported : Path.module_ option }

type occurrence = { span : Source.Definition_span.t; target : target }

val find_declared_name : Syntax.definition -> Syntax.name option
val list_named_members : Infer.tables -> Syntax.definition -> Path.t list

val list_occurrences :
  path:Path.t ->
  Source.Definition_span.t array ->
  Syntax.definition ->
  Resolve.resolved ->
  Infer.tables option ->
  occurrence list

val list_uses :
  resolve_module:(Syntax.path -> Path.module_) ->
  Syntax.path Syntax.item list ->
  (Path.module_ * Source.span) list

val is_named_by : Path.t -> target -> bool

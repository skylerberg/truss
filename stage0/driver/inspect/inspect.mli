module References : sig
  type target = References.target =
    | Definition of Path.t
    | Module of { module_ : Path.module_; imported : Path.module_ option }

  type occurrence = References.occurrence = { span : Source.Definition_span.t; target : target }

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
end

type unfinished = {
  keyword : [ `Todo | `Echo ];
  id : Syntax.id option;
  span : Source.Definition_span.t;
}

val list_unfinished : Source.Definition_span.t array -> Syntax.definition -> unfinished list

type hole = { offset : int; expected : string option; scope : (string * string) list }

val list_holes :
  Source.Definition_span.t array ->
  Syntax.definition ->
  Resolve.resolved ->
  Infer.tables option ->
  hole list

type explanation = {
  text : string;
  meaning : string option;
  refers_to : Path.t option;
  type_ : string option;
}

val explain_at :
  path:Path.t ->
  Source.Definition_span.t array ->
  Syntax.definition ->
  Resolve.resolved ->
  Infer.tables option ->
  text:string ->
  int ->
  explanation option

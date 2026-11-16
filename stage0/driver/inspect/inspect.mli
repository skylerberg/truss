module References = References

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

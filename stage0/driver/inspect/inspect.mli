module References = References

type unfinished = { keyword : [ `Todo | `Echo ]; id : Syntax.id option; span : Syntax.span }

val unfinished : Syntax.definition -> unfinished list

type explanation = {
  text : string;
  meaning : string option;
  refers_to : Path.t option;
  type_ : string option;
}

val explain_at :
  path:Path.t ->
  Syntax.definition ->
  Resolve.resolved ->
  Infer.tables option ->
  text:string ->
  int ->
  explanation option

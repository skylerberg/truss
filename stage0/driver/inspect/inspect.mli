module References = References

type unfinished = { keyword : [ `Todo | `Echo ]; id : Syntax.id option; span : Syntax.span }

val unfinished : (Resolve.Names.key, unfinished list) Query.query

type hole = { offset : int; expected : string option; scope : (string * string) list }

val holes : Query.context -> Resolve.Names.key -> hole list

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

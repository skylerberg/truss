type t = {
  definition : Resolve.Names.key -> Syntax.definition;
  spans : Resolve.Names.key -> Source.Definition_span.t array;
  text : Resolve.Names.key -> string;
  resolved : Resolve.Names.key -> Resolve.resolved;
  tables : Resolve.Names.key -> Infer.tables;
}

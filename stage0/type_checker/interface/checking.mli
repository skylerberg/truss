type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  elaborated : Environment.elaborated_interface;
  spans : Source.Definition_span.t array;
  diagnostics : Diagnostic.in_definition list ref;
}

val report :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  unit

val list_bounds : state -> Impls.bounds
val find_evidence : state -> Types.ty -> Types.trait_reference -> Impls.evidence option

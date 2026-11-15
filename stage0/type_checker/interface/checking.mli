type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  lowered : Environment.lowered_interface;
  mutable diagnostics : Diagnostic.in_definition list;
}

val report :
  state ->
  ?fixes:Source.Definition_span.t Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Source.Definition_span.t ->
  string ->
  unit

val bounds : state -> Types.parameter -> Types.trait_reference list
val implements : state -> Types.ty -> Types.trait_reference -> Impls.evidence option

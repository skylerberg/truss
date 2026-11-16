type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  elaborated : Environment.elaborated_interface;
  spans : Source.Definition_span.t array;
  diagnostics : Diagnostic.in_definition list ref;
}

let report state ?fixes code span message =
  ignore (Elaborator.record_diagnostic state.diagnostics ?fixes code span message)

let list_bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.elaborated.scope.bounds)

let find_evidence state type_ trait =
  Impls.find_evidence state.lookups ~list_bounds:(list_bounds state) type_ trait

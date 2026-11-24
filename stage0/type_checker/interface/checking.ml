type state = {
  lookups : Lookups.t;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  elaborated : Environment.elaborated_interface;
  spans : Source.Definition_span.t array;
  diagnostics : Catalog.description list ref;
}

let report state diagnostic = ignore (Elaborator.record_diagnostic state.diagnostics diagnostic)
let list_bounds state = Properties.Bounds.of_known state.elaborated.scope.bounds

let find_evidence state type_ trait =
  Impls.find_evidence state.lookups ~list_bounds:(list_bounds state) type_ trait

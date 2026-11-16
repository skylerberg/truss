open Syntax
module Names = Resolve.Names

type state = {
  lookups : Lookups.t;
  key : Names.key;
  definition : definition;
  elaborated : Environment.elaborated_interface;
  spans : Source.Definition_span.t array;
  diagnostics : Diagnostic.in_definition list ref;
}

let report state ?fixes code span message =
  ignore (Elaborator.record_diagnostic state.diagnostics ?fixes code span message)

let list_bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.elaborated.scope.bounds)

let implements state type_ trait =
  Impls.implements state.lookups ~bounds:(list_bounds state) type_ trait

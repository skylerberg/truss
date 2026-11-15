open Syntax
module Names = Resolve.Names

type state = {
  lookups : Lookups.t;
  key : Names.key;
  definition : definition;
  lowered : Environment.lowered_interface;
  mutable diagnostics : Diagnostic.in_definition list;
}

let reported state ?fixes code (span : Source.Definition_span.t) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

let bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.lowered.scope.bounds)

let implements state type_ trait = Impls.implements state.lookups ~bounds:(bounds state) type_ trait

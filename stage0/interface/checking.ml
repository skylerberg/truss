open Syntax
module Names = Resolve.Names

type state = {
  database : Query.context;
  key : Names.key;
  definition : definition;
  lowered : Environment.lowered_interface;
  mutable diagnostics : Syntax.diagnostic list;
}

let reported state ?fixes code (span : span) message =
  let diagnostic = Diagnostic.make ?fixes ~code:(Types code) span message in
  state.diagnostics <- diagnostic :: state.diagnostics;
  Diagnostic.reported diagnostic

let report state ?fixes code span message = ignore (reported state ?fixes code span message)

let bounds state parameter =
  Option.value ~default:[] (List.assoc_opt parameter state.lowered.bounds)

let implements state type_ trait =
  Impls.implements state.database ~bounds:(bounds state) type_ trait

(** The state of checking one definition's interface, and the helpers that report into it. *)

type state = {
  database : Query.context;
  key : Resolve.Names.key;
  definition : Syntax.definition;
  lowered : Environment.lowered_interface;
  mutable diagnostics : Syntax.diagnostic list;
}

val reported :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  Diagnostic.reported

val report :
  state ->
  ?fixes:Syntax.span Diagnostic.fix list ->
  Diagnostic.Code.types ->
  Syntax.span ->
  string ->
  unit

val bounds : state -> Types.parameter -> Types.trait_reference list
val implements : state -> Types.ty -> Types.trait_reference -> Impls.evidence option

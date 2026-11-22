val make_callee :
  Signatures.t ->
  Interface.Lookups.t ->
  list_bounds:Interface.Properties.Bounds.t ->
  Core.operand Core.target ->
  Core.callee

val make_call :
  Signatures.t ->
  Interface.Lookups.t ->
  list_bounds:Interface.Properties.Bounds.t ->
  callee:Core.operand Core.target ->
  arguments:Core.argument list ->
  lends:Language.Mode.t option ->
  Core.call

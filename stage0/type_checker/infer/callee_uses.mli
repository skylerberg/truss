val make_callee :
  Interface.Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  Core.operand Core.target ->
  Core.callee

val make_call :
  Interface.Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  callee:Core.operand Core.target ->
  arguments:Core.argument list ->
  lends:Language.Mode.t option ->
  Core.call

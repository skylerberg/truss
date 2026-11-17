val compute :
  Interface.Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  Core.callee ->
  Types.capability_set

val make_call :
  Interface.Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  callee:Core.callee ->
  arguments:Core.argument list ->
  lends:Types.mode option ->
  Core.call

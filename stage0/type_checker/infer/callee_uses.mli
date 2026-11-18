val instantiate : Interface.Lookups.t -> Core.operand Core.target -> Types.capability_set

val compute :
  Interface.Lookups.t ->
  list_bounds:(Types.parameter -> Types.trait_reference list) ->
  Core.operand Core.target ->
  Types.capability_set

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
  lends:Types.mode option ->
  Core.call

val add_restated_clauses :
  State.context ->
  self_type:Types.ty ->
  bind:(Types.trait_reference -> Path.t -> Types.substitution) ->
  Path.t ->
  string ->
  Path.receiver ->
  State.contract ->
  State.contract

val call_contract :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  Path.t ->
  State.contract ->
  State.passed list ->
  recursive_callee:Path.t option ->
  lent_final:(Logic.term -> Logic.term) option ->
  substitution_of:(State.clauses -> Types.substitution) ->
  type_arguments:Types.argument list ->
  State.frame * Logic.term

val apply_call :
  ?leave_lent:(Logic.term -> Logic.term) ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option

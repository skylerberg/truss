val add_restated_clauses :
  State.context ->
  self_type:Types.ty ->
  bind:(Types.trait_reference -> Path.t -> Types.substitution) ->
  Path.t ->
  string ->
  Path.receiver ->
  State.contract ->
  State.contract

type applied = {
  frame : State.frame;
  result : Logic.term;
  end_lend : (State.frame -> Logic.term -> State.frame) option;
}

val call_contract :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  Path.t ->
  State.contract ->
  State.passed list ->
  recursive_callee:Path.t option ->
  substitution_of:(State.clauses -> Types.substitution) ->
  type_arguments:Types.argument list ->
  applied

val apply_call :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option

val apply_lend :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  applied option

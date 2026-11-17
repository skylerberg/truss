val call_contract :
  ?is_constant_literal:bool ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  Path.t ->
  State.contract ->
  State.passed list ->
  lent_final:(Logic.term -> Logic.term) option ->
  havoc_mut:(State.frame -> State.frame) ->
  substitution_of:(State.part -> Types.substitution) ->
  instance:Types.argument list ->
  State.frame * Logic.term

val make_time_term : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term

val apply_call :
  ?leave_lent:(Logic.term -> Logic.term) ->
  ?is_constant_literal:bool ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option

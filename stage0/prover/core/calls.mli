(** A call: through the callee's contract, or for an intrinsic, its meaning. *)

val contract_call :
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
  instance:string list ->
  State.frame * Logic.term

val time_of : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term

val apply_call :
  ?lent_final:(Logic.term -> Logic.term) ->
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  through:(Types.ty * Logic.term * Invocation.shape) option ->
  State.passed list ->
  (State.frame * Logic.term) option

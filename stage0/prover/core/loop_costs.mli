type t

val enter :
  State.frame ->
  entry:State.frame ->
  Mir.loop_clause list ->
  holds:State.changed_part list ->
  changed:State.changed_part list ->
  t

val declare_iterations : State.frame -> t -> Logic.term option
val enter_head : State.frame -> t -> iterations:Logic.term option -> State.frame
val spend_step : State.frame -> State.frame

val check_iterations :
  Core.origin ->
  State.frame ->
  t ->
  iterations:Logic.term option ->
  iteration_bounds:Logic.term list ->
  inside:State.frame ->
  ends:State.frame list ->
  breaks:State.frame list ->
  unit

val leave :
  clause_at:State.frame ->
  State.frame ->
  t ->
  iterations:Logic.term option ->
  most:Logic.term list ->
  State.frame

val leave_counted :
  Query.t ->
  clause_at:State.frame ->
  State.frame ->
  t ->
  iterations:Logic.term option ->
  most:Logic.term list ->
  count:Logic.term ->
  since:Query.mark ->
  State.frame

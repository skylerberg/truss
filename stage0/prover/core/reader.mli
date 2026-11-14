(** The reader of the MIR: runs a body's blocks forward from a frame, and maps a formula to a term,
    by the rules. *)

val formula_term :
  State.context ->
  State.frame ->
  Mir.formula ->
  arguments:Logic.term list ->
  State.frame * Logic.term

val mir_run : State.context -> State.frame -> lambdas:Mir.body array -> Mir.body -> unit

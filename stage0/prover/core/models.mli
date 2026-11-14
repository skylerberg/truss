(** The logic's sequences, the model of a collection, and quantifiers. *)

val under_binder :
  State.context ->
  State.frame ->
  Logic.symbol ->
  Logic.sort ->
  Logic.term ->
  (State.frame -> 'read) ->
  State.frame * 'read * (Logic.term -> Logic.term)

val sequence_path : Path.t
val sequence_type : Types.ty -> Types.ty
val sequence_length : State.context -> Types.ty -> Logic.term -> Logic.term
val sequence_at : State.context -> Types.ty -> Logic.term -> Logic.term -> Logic.term option
val rank : State.context -> Types.ty -> Logic.term -> Logic.term

val finite_function :
  State.context ->
  Types.ty ->
  string ->
  Logic.sort ->
  (Logic.term * Logic.sort) list ->
  Logic.term ->
  Logic.term

val finite_set_path : Path.t
val model_ranked : State.context -> Types.ty -> model:Types.ty -> Logic.symbol -> unit

val model_function :
  State.context -> Types.ty -> model:Types.ty -> (Logic.term -> Logic.term) option

val model_of : State.context -> Types.ty -> Logic.term -> element:Types.ty -> Logic.term option

val quantified_over :
  State.context ->
  State.frame ->
  Syntax.quantifier ->
  State.quantified_range ->
  bind:(State.frame -> Logic.term -> Types.ty -> Logic.term * State.frame) ->
  read:(State.frame -> Logic.term -> State.frame * Logic.term) ->
  (State.frame * Logic.term) option

val value_term : State.context -> State.frame -> Types.value -> Logic.term

val generic_argument :
  State.context ->
  State.frame ->
  Intrinsic.operation ->
  Types.argument list ->
  string ->
  Logic.term option

val array_model : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term

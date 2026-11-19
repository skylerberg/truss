type quantified_range =
  | Range_of_type of Types.ty
  | Range_of_integers of { low : Logic.term; high : Logic.term; inclusive : bool; type_ : Types.ty }

val run_under_binder :
  State.context ->
  State.frame ->
  Logic.symbol ->
  Logic.sort ->
  Logic.term ->
  (State.frame -> 'read) ->
  State.frame * 'read * (Logic.term -> Logic.term)

val sequence_path : Path.t
val make_sequence_type : Types.ty -> Types.ty
val make_sequence_length : State.context -> Types.ty -> Logic.term -> Logic.term
val index_sequence : State.context -> Types.ty -> Logic.term -> Logic.term -> Logic.term option
val rank : State.context -> Types.ty -> Logic.term -> Logic.term

val make_finite_function :
  State.context ->
  Types.ty ->
  string ->
  Logic.sort ->
  (Logic.term * Logic.sort) list ->
  Logic.term ->
  Logic.term

val finite_set_path : Path.t
val rank_model : State.context -> Types.ty -> model:Types.ty -> impl:Path.t -> Logic.symbol -> unit

val find_model_function :
  State.context -> Types.ty -> model:Types.ty -> (Logic.term -> Logic.term) option

val find_model : State.context -> Types.ty -> Logic.term -> element:Types.ty -> Logic.term option

val quantify_over :
  State.context ->
  State.frame ->
  Core.quantifier ->
  quantified_range ->
  bind:(State.frame -> Logic.term -> Types.ty -> State.frame) ->
  read:(State.frame -> Logic.term -> State.frame * Logic.term) ->
  State.frame * Logic.term

val make_value_term : State.context -> State.frame -> Types.value -> Logic.term
val make_array_model : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term

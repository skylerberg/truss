type quantified_range =
  | Range_of_type of Types.ty
  | Range_of_integers of { low : Logic.term; high : Logic.term; inclusive : bool; type_ : Types.ty }

val run_under_binder :
  State.frame ->
  Logic.symbol ->
  Logic.sort ->
  Logic.term ->
  (State.frame -> 'read) ->
  State.frame * 'read * (Logic.term -> Logic.term)

val make_sequence_length : Types.ty -> Logic.term -> Logic.term

val index_sequence :
  State.environment -> Query.t -> Types.ty -> Logic.term -> Logic.term -> Logic.term option

val rank : State.environment -> Query.t -> Types.ty -> Logic.term -> Logic.term

val make_finite_function :
  Query.t ->
  Well_known.method_ ->
  arguments:Types.argument list ->
  Logic.sort ->
  (Logic.term * Logic.sort) list ->
  Logic.term ->
  Logic.term

val rank_model :
  State.environment -> Query.t -> Types.ty -> model:Types.ty -> impl:Path.t -> Logic.symbol -> unit

val find_model_function :
  State.environment -> Query.t -> Types.ty -> model:Types.ty -> (Logic.term -> Logic.term) option

val find_model :
  State.environment -> Query.t -> Types.ty -> Logic.term -> element:Types.ty -> Logic.term option

val quantify_over :
  State.frame ->
  Language.Quantifier.t ->
  quantified_range ->
  bind:(State.frame -> Logic.term -> Types.ty -> State.frame) ->
  read:(State.frame -> Logic.term -> State.frame * Logic.term) ->
  State.frame * Logic.term

val make_value_term : State.frame -> Types.value -> Logic.term
val make_array_model : State.frame -> Types.ty -> Logic.term -> Logic.term

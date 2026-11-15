val compared_terms : Types.ty -> Core.comparison -> Logic.term -> Logic.term -> Logic.term
val check_widened : Source.Definition_span.t -> is_written:bool -> Types.ty -> Types.ty -> unit
val from_integer : State.context -> State.frame -> Invocation.site -> Logic.term -> Logic.term
val spend : State.context -> State.frame -> (Costs.counter -> Logic.term) -> State.frame
val unknown_amount : State.context -> State.frame -> Costs.counter -> Logic.term
val to_any : State.context -> State.frame -> Invocation.site -> State.frame * Logic.term
val current_bounds : State.context -> Interface.Impls.bounds

val concrete_impl :
  State.context -> Types.trait_reference -> Types.ty -> (Path.t * Types.substitution) option

val equal_of : State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term
val innermost_axiom : State.context -> State.frame -> Logic.term -> State.open_axiom option
val power_of : State.context -> State.frame -> Logic.term -> Logic.term -> Logic.term

val primitive_operation :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  Intrinsic.operation ->
  Types.ty list ->
  Logic.term list ->
  arguments:Core.origin option list ->
  fallback:(unit -> Logic.term) ->
  Logic.term

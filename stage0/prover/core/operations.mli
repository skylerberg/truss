val compare_terms : Types.ty -> Language.Comparison.t -> Logic.term -> Logic.term -> Logic.term
val check_widened : Obligation.location -> is_written:bool -> Types.ty -> Types.ty -> unit

val convert_from_integer :
  State.context -> State.frame -> Invocation.site -> Logic.term -> Logic.term

val spend : State.context -> State.frame -> (Costs.counter -> Logic.term) -> State.frame
val declare_unknown_amount : State.context -> State.frame -> Costs.counter -> Logic.term
val convert_to_any : State.context -> State.frame -> Invocation.site -> State.frame * Logic.term
val compute_current_bounds : State.context -> Interface.Impls.bounds

val find_concrete_impl :
  State.context -> Types.trait_reference -> Types.ty -> (Path.t * Types.substitution) option

val make_equality :
  State.context -> State.frame -> Types.ty -> Logic.term -> Logic.term -> Logic.term

val find_innermost_axiom : State.context -> State.frame -> Logic.term -> State.open_axiom option
val declare_power : State.context -> State.frame -> Logic.term -> Logic.term -> Logic.term

val translate_primitive_operation :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  Intrinsic.scalar ->
  Types.ty list ->
  Logic.term list ->
  arguments:Core.origin option list ->
  fallback:(unit -> Logic.term) ->
  Logic.term

(** Bodies read whole, and what a call costs: a callee's bounds, a value's potential, and a method's
    time. *)

val definition_value : State.context -> State.frame -> Mir.formula -> State.frame * Logic.term

val body_over :
  State.context ->
  State.frame ->
  (Logic.symbol * 'a) list ->
  Mir.formula ->
  (State.frame -> State.frame) ->
  Logic.term option

val without_temporaries : 'a State.Locals.t -> 'a State.Locals.t

val body_run :
  State.context ->
  State.frame ->
  lambdas:Mir.body array ->
  Mir.body ->
  type_:Types.ty ->
  (State.frame * Logic.term) option

val code_value : State.context -> State.frame -> Mir.t -> type_:Types.ty -> State.frame * Logic.term
val default_value : State.context -> State.frame -> State.part -> int -> Logic.term
val named_term : State.context -> Types.ty -> Logic.term -> Logic.term
val empty_parts : State.context -> State.frame -> Types.ty -> Logic.term
val mentions_result : Mir.formula -> bool
val mentions_history : Mir.formula -> bool
val assume_typed : State.context -> State.frame -> Logic.term -> unit

val requires_fix :
  State.context ->
  State.frame ->
  State.part ->
  Mir.requirement ->
  Logic.term ->
  State.passed list ->
  Syntax.Span.t Diagnostic.fix list

val note_known_call :
  State.context -> Invocation.t -> Path.t -> Logic.term -> Logic.term list -> unit

val structural_parameters :
  State.context -> State.frame -> State.part -> (Types.ty * Logic.term * int) list

val argument_at_index : State.passed list -> int -> Logic.term
val lexicographically_less : Logic.term list -> Logic.term list -> Logic.term
val same_resource : Mir.cost -> locals:Logic.term State.Locals.t -> Costs.counter -> bool
val bounded_amount : State.context -> State.frame -> Logic.term -> Logic.term

val may_be_target :
  State.context -> State.frame -> Logic.term -> Types.ty -> Logic.term -> Logic.term

val lambda_captures_target : State.context -> Logic.term -> Logic.term -> bool
val spent_where : Logic.term -> Logic.term -> Logic.term

val callee_amount :
  ?ends_in:Logic.term ->
  State.context ->
  State.frame ->
  path:Path.t ->
  parts:State.part list ->
  bound_frame:(State.part -> State.frame) ->
  uses:Types.capability list ->
  values:State.passed list ->
  change:(unit -> Logic.term) option ->
  Costs.counter ->
  Logic.term

val step_amount :
  State.context -> State.frame -> Invocation.t -> State.passed list -> Costs.counter -> Logic.term

val has_potential : State.context -> ?seen:Types.ty list -> Types.ty -> bool

val potential :
  State.context -> State.frame -> ?seen:Types.ty list -> Types.ty -> Logic.term -> Logic.term

val trait_method_time : State.context -> State.frame -> Path.t -> Types.ty -> Logic.term
val method_time : State.context -> State.frame -> Invocation.callee -> Logic.term

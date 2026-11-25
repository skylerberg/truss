val apply_function :
  State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term

val is_in_the_logic : Types.function_type -> bool
val read_output : Types.function_type -> Types.ty

val make_callback_ensures :
  State.context ->
  Types.function_type ->
  Logic.term ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  Logic.term

val apply_callback_ensures : State.context -> Types.function_type -> Logic.term list -> Logic.term

val make_parameter_symbols :
  State.context -> State.frame -> Types.function_type -> ('a Logic.Symbol.t * Logic.sort) list

val prove_panic_condition :
  State.context -> State.frame -> Validity.callback option -> (State.frame -> 'a) -> unit

val oblige_callback_promises :
  State.context ->
  State.frame ->
  Obligation.location ->
  Validity.promise list ->
  passed:Catalog.Prover.passed_function ->
  exits:Logic.term list ->
  result:Logic.term ->
  yielded:Logic.term option ->
  unit

val oblige_callback_costs :
  State.context ->
  State.frame ->
  Obligation.location ->
  Validity.callback ->
  passed:Catalog.Prover.passed_function ->
  unit

val check_valid :
  State.context ->
  State.frame ->
  Obligation.location ->
  Types.ty ->
  Logic.term ->
  deep:bool ->
  moment:Catalog.Prover.invariant_moment ->
  unit

val remove_temporaries : 'a Locals.t -> 'a Locals.t

val run_lambda_body :
  ?enter:(State.frame -> State.frame) ->
  State.context ->
  State.frame ->
  lambdas:Mir.body array ->
  Mir.body ->
  type_:Types.ty ->
  (State.frame * Logic.term) option

val list_loop_counters :
  State.context -> Logic.term Locals.t -> Mir.body -> (Costs.counter * Types.condition) list

val assign_counters : State.context -> (Costs.counter * Types.condition) list -> unit
val list_facts_since : State.context -> int -> Logic.term list

val translate_lambda :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  State.lambda_code ->
  find_callback:(Logic.term list -> Validity.callback) option ->
  State.frame * Logic.term

val make_passed_values :
  State.context -> State.frame -> Invocation.t -> State.call_argument list -> State.passed list

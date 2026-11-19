val apply_function :
  State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term

val is_in_the_logic : Types.function_type -> bool

val make_parameter_symbols :
  State.context -> State.frame -> Types.function_type -> ('a Logic.Symbol.t * Logic.sort) list

val check_valid :
  State.context ->
  State.frame ->
  Obligation.location ->
  Types.ty ->
  Logic.term ->
  deep:bool ->
  when_:string ->
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

val classify_counting : Mir.cost -> Costs.counting
val list_loop_counters : Logic.term Locals.t -> Mir.body -> Costs.counter list
val list_facts_since : State.context -> int -> Logic.term list

val translate_lambda :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  State.lambda_code ->
  list_facts:(Logic.term list -> Logic.term list) ->
  State.frame * Logic.term

val make_passed_values :
  State.context -> State.frame -> Invocation.t -> State.call_argument list -> State.passed list

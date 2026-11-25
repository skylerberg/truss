val apply_function :
  State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term

val is_in_the_logic : Types.function_type -> bool

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

val run_code : State.context -> State.frame -> Mir.t -> type_:Types.ty -> State.frame * Logic.term

val translate_lambda :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  State.lambda_code ->
  list_facts:(Logic.term list -> Logic.term list) ->
  list_promises:
    (entries:Logic.term list ->
    exits:Logic.term list ->
    result:Logic.term ->
    (Catalog.Prover.quoted * Logic.term) list) ->
  State.frame * Logic.term

val make_passed_values :
  State.context -> State.frame -> Invocation.t -> State.call_argument list -> State.passed list

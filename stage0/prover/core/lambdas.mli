val make_parameter_symbols :
  State.context -> State.frame -> Types.function_type -> ('a Logic.Symbol.t * Logic.sort) list

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
  State.context -> State.frame -> Callee.t -> State.call_argument list -> State.passed list

val remove_temporaries : 'a Locals.t -> 'a Locals.t

val run_lambda_body :
  ?enter:(State.frame -> State.frame) ->
  State.frame ->
  lambdas:Mir.body array ->
  Mir.body ->
  type_:Types.ty ->
  (State.frame * Logic.term) option

val run_code : State.frame -> Mir.t -> type_:Types.ty -> State.frame * Logic.term

val translate_lambda :
  State.frame ->
  site:Invocation.site ->
  State.lambda_code ->
  stated:Callbacks.parameter_contract ->
  State.frame * Logic.term

val make_passed_values :
  State.frame -> at:Core.origin -> Callee.t -> State.call_argument list -> State.passed list

(** Lambdas: a lambda's body, proven where it is written, and a functional lambda as a function of
    the logic. *)

val applied : State.context -> Types.function_type -> Logic.term -> Logic.term list -> Logic.term
val in_the_logic : Types.function_type -> bool

val parameters_of :
  State.context -> State.frame -> Types.function_type -> ('a State.Symbol.t * Logic.sort) list

val check_valid :
  State.context ->
  State.frame ->
  State.span ->
  Types.ty ->
  Logic.term ->
  deep:bool ->
  when_:string ->
  unit

val counting_of : Mir.cost -> Costs.counting
val mir_loop_counters : Logic.term State.Locals.t -> Mir.body -> Costs.counter list
val facts_since : State.context -> int -> Logic.term list

val lambda :
  State.context ->
  State.frame ->
  site:Invocation.site ->
  State.lambda_code ->
  facts:(Logic.term list -> Logic.term list) ->
  State.frame * Logic.term

val passed_values :
  State.context -> State.frame -> Invocation.t -> State.given list -> State.passed list

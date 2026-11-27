val read_formula :
  State.frame -> Mir.formula -> arguments:Logic.term list -> State.frame * Logic.term

val read_body : State.frame -> lambdas:Mir.body array -> Mir.body -> State.body_exits

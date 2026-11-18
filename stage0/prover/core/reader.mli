val read_formula :
  State.context ->
  State.frame ->
  Mir.formula ->
  arguments:Logic.term list ->
  State.frame * Logic.term

val read_body :
  State.context ->
  State.frame ->
  lambdas:Mir.body array ->
  Mir.body ->
  (State.frame * Logic.term option) list

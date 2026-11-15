val definition_span : State.source -> Syntax.Span.t

val function_ :
  ?proof:bool ->
  ?is_updating_helper:bool ->
  ?inherited:State.part * Types.substitution * Mir.definition option ->
  ?substitution:Types.substitution ->
  Query.context ->
  State.source ->
  path:Path.t ->
  State.outcome

val laws :
  Query.context ->
  State.source ->
  impl:Path.t ->
  trait:Types.trait_reference ->
  for_type:Types.ty ->
  proofs:(string * (State.source * Types.substitution)) list ->
  at:State.span ->
  State.outcome

val type_ : Query.context -> State.source -> path:Path.t -> State.outcome
val test : Query.context -> State.source -> path:Path.t -> State.outcome
val constant : Query.context -> State.source -> path:Path.t -> State.outcome
val theorem : Query.context -> State.source -> path:Path.t -> State.outcome

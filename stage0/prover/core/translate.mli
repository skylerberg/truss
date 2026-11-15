val definition_span : State.source -> Source.Definition_span.t

val function_ :
  ?proof:bool ->
  ?is_updating_helper:bool ->
  ?inherited:State.part * Types.substitution ->
  ?substitution:Types.substitution ->
  Lookups.t ->
  State.source ->
  path:Path.t ->
  State.outcome

val laws :
  Lookups.t ->
  State.source ->
  impl:Path.t ->
  trait:Types.trait_reference ->
  for_type:Types.ty ->
  proofs:(string * (State.source * Types.substitution)) list ->
  at:Source.Definition_span.t ->
  State.outcome

val type_ : Lookups.t -> State.source -> path:Path.t -> State.outcome
val test : Lookups.t -> State.source -> path:Path.t -> State.outcome
val constant : Lookups.t -> State.source -> path:Path.t -> State.outcome
val theorem : Lookups.t -> State.source -> path:Path.t -> State.outcome

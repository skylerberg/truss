val translate_function :
  ?proof:bool ->
  ?inherited:State.clauses * Types.substitution ->
  ?substitution:Types.substitution ->
  Lookups.t ->
  State.source ->
  path:Path.t ->
  Obligation.outcome

val translate_laws :
  Lookups.t ->
  State.source ->
  impl:Path.t ->
  trait:Types.trait_reference ->
  for_type:Types.ty ->
  proofs:(string * (State.source * Types.substitution)) list ->
  at:Obligation.location ->
  Obligation.outcome

val translate_type : Lookups.t -> State.source -> path:Path.t -> Obligation.outcome
val translate_constant : Lookups.t -> State.source -> path:Path.t -> Obligation.outcome
val translate_theorem : Lookups.t -> State.source -> path:Path.t -> Obligation.outcome

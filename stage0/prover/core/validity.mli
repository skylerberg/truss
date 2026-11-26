type place_value = One of Logic.term | Run of Logic.term * Logic.term

val note_place : State.frame -> node:Core.id -> origin:Core.origin -> place_value -> unit

val run_as_specification :
  State.frame -> (State.frame -> State.frame * 'value) -> State.frame * 'value

val read_specification :
  ?holds_when:Types.condition -> State.frame -> Mir.formula -> State.frame * Logic.term

val check_defined : State.frame -> holds_when:Types.condition -> Mir.formula -> unit

val make_type_frame :
  State.frame -> State.source -> Types.ty -> self:Logic.term option -> State.frame

val find_type_source : State.environment -> Types.ty -> State.source option
val find_type_clauses : State.environment -> Types.ty -> (State.source * Mir.type_clauses) option
val list_invariants : Mir.loop_clause list -> Mir.formula list
val find_invariants : State.environment -> Types.ty -> (State.source * Mir.formula list) option

val make_validity :
  State.frame ->
  assuming:bool ->
  ?deep:bool ->
  ?includes_invariants:bool ->
  ?includes_ranges:bool ->
  ?seen:Types.ty list ->
  Types.ty ->
  Logic.term ->
  Logic.term

val assume_valid : ?includes_invariants:bool -> State.frame -> Types.ty -> Logic.term -> unit

val check_valid :
  ?includes_invariants:bool ->
  State.frame ->
  Obligation.location ->
  Types.ty ->
  Logic.term ->
  deep:bool ->
  moment:Catalog.Prover.invariant_moment ->
  unit

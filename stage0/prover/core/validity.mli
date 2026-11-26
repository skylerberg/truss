val make_state : unit -> State.validity_state

val note_place :
  State.context -> State.frame -> node:Core.id -> origin:Core.origin -> State.place_value -> unit

val run_as_specification : State.context -> (unit -> 'a) -> 'a
val read_specification : State.context -> State.frame -> Mir.formula -> State.frame * Logic.term

val check_defined :
  State.context -> State.frame -> holds_when:Types.condition -> Mir.formula -> unit

val select_field : State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val replace_field :
  State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term -> Logic.term

val find_root : State.context -> State.frame -> Locals.local -> (Types.ty * Logic.term) option

val find_changed_part :
  State.context -> State.frame -> State.changed_part -> (Types.ty * Logic.term) option

val replace_part :
  State.context ->
  Types.ty ->
  Logic.term ->
  string list ->
  (Types.ty -> Logic.term -> Logic.term) ->
  Logic.term option

val make_type_frame :
  State.context -> State.frame -> State.source -> Types.ty -> self:Logic.term option -> State.frame

val find_type_source : State.context -> Types.ty -> State.source option
val find_type_clauses : State.context -> Types.ty -> (State.source * Mir.type_clauses) option
val list_invariants : Mir.loop_clause list -> Mir.formula list
val find_invariants : State.context -> Types.ty -> (State.source * Mir.formula list) option

val make_validity :
  State.context ->
  State.frame ->
  assuming:bool ->
  ?deep:bool ->
  ?includes_invariants:bool ->
  ?seen:Types.ty list ->
  Types.ty ->
  Logic.term ->
  Logic.term

val find_parts_in_range :
  State.context -> ?seen:Types.ty list -> Types.ty -> Logic.term -> Logic.term option

val assume_valid :
  ?includes_invariants:bool -> State.context -> State.frame -> Types.ty -> Logic.term -> unit

val check_valid :
  ?includes_invariants:bool ->
  State.context ->
  State.frame ->
  Obligation.location ->
  Types.ty ->
  Logic.term ->
  deep:bool ->
  moment:Catalog.Prover.invariant_moment ->
  unit

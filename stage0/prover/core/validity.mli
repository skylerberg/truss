(** What holds of a value because of its type, and of a callback because of its parameter: a type's
    invariants, a function-typed parameter's clauses, and the places that must be disjoint. *)

val note_place : State.context -> State.frame -> int -> State.place_value -> unit
val without_costs : State.context -> (unit -> 'a) -> 'a
val specification_value : State.context -> State.frame -> Mir.formula -> State.frame * Logic.term
val selected : State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val type_frame :
  State.context -> State.frame -> State.source -> Types.ty -> self:Logic.term option -> State.frame

val type_source : State.context -> Types.ty -> State.source option
val type_clauses : State.context -> Types.ty -> (State.source * Mir.type_clauses) option
val invariants : Mir.loop_clause list -> Mir.formula list
val invariants_of : State.context -> Types.ty -> (State.source * Mir.formula list) option

val validity :
  State.context ->
  State.frame ->
  assuming:bool ->
  ?deep:bool ->
  ?own:bool ->
  ?seen:Types.ty list ->
  Types.ty ->
  Logic.term ->
  Logic.term

val assume_valid : State.context -> State.frame -> Types.ty -> Logic.term -> unit
val callback_arguments : State.context -> State.frame -> ('a * Types.ty) list -> Logic.term list

val callback_contract_frame :
  State.frame -> (State.Locals.key * 'a) list -> Logic.term list -> State.frame

val own_callback : State.context -> Core.local -> (string * Mir.callback) option
val escaping_callback : State.context -> State.frame -> State.Locals.key -> unit
val reading_callback : State.context -> (unit -> 'a) -> 'a

val part_frame :
  State.frame ->
  State.part ->
  arguments:(int * Logic.term) list ->
  substitution:Types.substitution ->
  State.frame

val callback_facts :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  Logic.term list ->
  Logic.term list

val parameter_type : State.context -> State.frame -> Invocation.t -> int -> Types.ty option

val check_forwarded_callback :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  State.passed ->
  State.Locals.key ->
  State.passed list ->
  unit

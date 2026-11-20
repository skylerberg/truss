val note_place :
  State.context -> State.frame -> node:Core.id -> origin:Core.origin -> State.place_value -> unit

val run_without_costs : State.context -> (unit -> 'a) -> 'a
val read_specification : State.context -> State.frame -> Mir.formula -> State.frame * Logic.term
val select_field : State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val make_type_frame :
  State.context -> State.frame -> State.source -> Types.ty -> self:Logic.term option -> State.frame

val find_type_source : State.context -> Types.ty -> State.source option
val find_type_clauses : State.context -> Types.ty -> (State.source * Mir.type_clauses) option
val list_invariants : Mir.loop_clause list -> Mir.formula list
val find_invariants : State.context -> Types.ty -> (State.source * Mir.invariant list) option

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

val assume_valid : State.context -> State.frame -> Types.ty -> Logic.term -> unit
val run_validating : State.context -> Types.ty -> (unit -> 'a) -> 'a

val declare_callback_arguments :
  State.context -> State.frame -> ('a * Types.ty) list -> Logic.term list

val make_callback_contract_frame : State.frame -> Core.local list -> Logic.term list -> State.frame
val find_own_callback : State.context -> Core.local -> (string * Mir.callback) option
val check_escaping_callback : State.context -> State.frame -> Core.local -> unit
val run_reading_callback : State.context -> (unit -> 'a) -> 'a

val bind_arguments :
  State.frame ->
  State.clauses ->
  arguments:(int * Logic.term) list ->
  substitution:Types.substitution ->
  State.frame

val list_callback_facts :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  Logic.term list ->
  Logic.term list

val find_parameter_type : State.context -> State.frame -> Invocation.t -> int -> Types.ty option

val make_callback_ensures_frame :
  State.frame ->
  Core.local list ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  State.frame

val list_callback_promises :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  (Obligation.piece * Logic.term) list

val assume_own_callback_ensures :
  State.context ->
  State.frame ->
  Core.local ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit

val declare_callback_results :
  State.context ->
  State.frame ->
  Types.function_type ->
  Logic.term list ->
  Logic.term list * Logic.term

val check_callback_promises :
  State.context ->
  State.frame ->
  location:Obligation.location ->
  Invocation.t ->
  State.passed ->
  described:string ->
  assume:
    (State.frame ->
    Types.function_type ->
    entries:Logic.term list ->
    exits:Logic.term list ->
    result:Logic.term ->
    unit) ->
  State.passed list ->
  unit

val assume_nothing :
  State.frame ->
  Types.function_type ->
  entries:Logic.term list ->
  exits:Logic.term list ->
  result:Logic.term ->
  unit

val check_forwarded_callback :
  State.context ->
  State.frame ->
  Invocation.site ->
  Invocation.t ->
  State.passed ->
  Core.local ->
  State.passed list ->
  unit

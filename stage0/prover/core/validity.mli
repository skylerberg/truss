val note_place :
  State.context -> State.frame -> node:Core.id -> origin:Core.origin -> State.place_value -> unit

val run_without_costs : State.context -> (unit -> 'a) -> 'a
val run_as_specification : State.context -> (unit -> 'a) -> 'a
val read_specification : State.context -> State.frame -> Mir.formula -> State.frame * Logic.term
val select_field : State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term

val replace_field :
  State.context -> Types.ty -> string option -> string -> Logic.term -> Logic.term -> Logic.term

val find_part :
  State.context -> Types.ty -> Logic.term -> string list -> (Types.ty * Logic.term) option

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

val assume_valid : State.context -> State.frame -> Types.ty -> Logic.term -> unit

val declare_callback_arguments :
  State.context -> State.frame -> ('a * Types.ty) list -> Logic.term list

val find_own_callback : State.context -> Core.local -> (string * Mir.contract) option
val make_callback_clauses : State.frame -> Mir.contract option -> State.clauses
val check_escaping_callback : State.context -> State.frame -> Core.local -> unit
val run_reading_callback : State.context -> (unit -> 'a) -> 'a

val bind_arguments :
  State.frame ->
  State.clauses ->
  arguments:(int * Logic.term) list ->
  substitution:Types.substitution ->
  State.frame

val find_parameter_type : State.context -> State.frame -> Invocation.t -> int -> Types.ty option
val find_parameter_name : State.context -> State.frame -> Invocation.t -> int -> string
val classify_counting : Mir.cost -> Costs.counting

type promise = {
  clause : Mir.formula;
  quoted : Catalog.Prover.quoted;
  read : exits:Logic.term list -> result:Logic.term -> yielded:Logic.term option -> Logic.term;
}

type callback = {
  parameter : string;
  requires : Logic.term list;
  panic_condition : Catalog.Prover.quoted list * Logic.term list;
  costs : (Costs.counter * Logic.term * Catalog.Prover.quoted) list;
  promises : promise list;
}

val find_callback :
  State.context ->
  State.frame ->
  Invocation.t ->
  int ->
  (int * Logic.term) list ->
  (Logic.term list -> callback) option

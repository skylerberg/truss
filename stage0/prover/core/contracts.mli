val read_source_at_key : Lookups.t -> Resolve.Names.key -> State.source

val find_source :
  Lookups.t -> Path.t -> (State.source * Types.substitution * Interface.form_origin) option

val make_trait_substitution : Lookups.t -> Types.trait_reference -> Types.ty -> Types.substitution

val list_law_proofs :
  Lookups.t ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * (State.source * Types.substitution)) list

val list_impl_holes :
  Lookups.t -> Resolve.Names.key -> (Resolve.Names.key * Obligation.location) list

val has_impl_obligations : Lookups.t -> Path.t -> bool

val list_law_holes :
  Lookups.t ->
  Path.t ->
  Types.trait_reference ->
  Types.ty ->
  string ->
  (Resolve.Names.key * Obligation.location) list

val list_declared_clauses : State.contract -> State.clauses list
val select_precondition_clauses : State.contract -> State.clauses
val find_declared_clauses : Lookups.t -> Path.t -> State.clauses option
val read_signature : State.context -> Path.t -> Types.signature option
val find_callee_clauses : State.context -> Path.t -> State.clauses option
val list_modified_fields : State.context -> Path.t -> int -> string list list option
val find_function_contract : State.context -> Path.t -> State.contract option
val find_capability_contract : State.context -> Path.t -> string -> State.contract option
val find_capability_clauses : State.context -> Path.t -> string -> State.clauses option

val list_restated_clauses :
  State.context ->
  packages:Path.package list ->
  self_type:Types.ty ->
  Path.t ->
  string ->
  Path.receiver ->
  (Types.trait_reference * State.clauses) list

val find_method_contract :
  State.context ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  Types.evidence ->
  State.contract option

val find_integer_literal : Mir.formula -> Z.t option
val deduplicate_counters : 'a list -> 'a list
val find_resource : Mir.cost -> locals:Logic.term Locals.t -> Costs.resource option

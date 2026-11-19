val read_source_at_key : Lookups.t -> Resolve.Names.key -> State.source

val find_source :
  Lookups.t -> Path.t -> (State.source * Types.substitution * Interface.form_origin) option

val make_trait_substitution : Lookups.t -> Types.trait_reference -> Types.ty -> Types.substitution
val find_clauses : Lookups.t -> Path.t -> State.source -> State.clauses option

val list_law_proofs :
  Lookups.t ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * (State.source * Types.substitution)) list

val is_impl_unfinished : Lookups.t -> Resolve.Names.key -> bool
val is_law_unshown : Lookups.t -> Path.t -> Types.trait_reference -> Types.ty -> string -> bool
val list_declared_clauses : State.contract -> State.clauses list
val select_precondition_clauses : State.contract -> State.clauses
val find_function_contract : Lookups.t -> Path.t -> State.contract option
val find_declared_clauses : Lookups.t -> Path.t -> State.clauses option
val find_capability_contract : Lookups.t -> Path.t -> string -> State.contract option
val find_capability_clauses : Lookups.t -> Path.t -> string -> State.clauses option

val find_method_contract :
  Lookups.t ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  Core.evidence ->
  State.contract option

val find_integer_literal : Mir.formula -> Z.t option
val deduplicate_counters : 'a list -> 'a list
val find_resource : Mir.cost -> locals:Logic.term Locals.t -> Costs.resource option
val find_comparison_operator : Core.comparison -> string option

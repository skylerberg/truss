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

val select_precondition_clauses : State.contract -> State.clauses

type premise = The_precondition | Requires_of of State.clauses
type promise = { made_by : State.clauses; proven_under : premise }

val list_promises : State.contract -> promise list
val find_declared_clauses : Lookups.t -> Path.t -> State.clauses option
val read_signature : State.environment -> Path.t -> Types.signature option
val find_callee_clauses : State.environment -> Path.t -> State.clauses option
val list_modified_parts : State.environment -> Path.t -> int -> Types.modified list option

val find_inherited_clauses :
  State.environment -> Path.t -> (State.clauses * Types.substitution) option

val list_added_clauses : State.environment -> Path.t -> (State.clauses * Types.substitution) list
val find_function_contract : State.environment -> Path.t -> State.contract option
val find_capability_contract : State.environment -> Path.t -> string -> State.contract option

val list_restated_clauses :
  State.environment ->
  packages:Path.package list ->
  self_type:Types.ty ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  (Types.trait_reference * State.clauses) list

val find_method_contract :
  State.environment ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  Types.evidence ->
  State.contract option

val find_integer_literal : Mir.formula -> Z.t option
val mentions_specification : Mir.formula -> (Mir.specification -> bool) -> bool
val mentions_result : Mir.formula -> bool
val mentions_visited : Mir.formula -> bool
val mentions_final_result : Mir.formula -> bool
val find_promiser : Lookups.t -> State.source -> Catalog.Prover.promiser

val make_entry_frame :
  State.frame ->
  State.clauses ->
  arguments:(int * Logic.term) list ->
  substitution:Types.substitution ->
  State.frame

val make_exit_frame :
  State.frame ->
  State.clauses ->
  entries:(int * Logic.term) list ->
  exits:(int * Logic.term) list ->
  result:Logic.term option ->
  substitution:Types.substitution ->
  State.frame

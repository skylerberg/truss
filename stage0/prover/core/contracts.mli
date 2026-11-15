val source_at_key : Lookups.t -> State.Names.key -> State.source
val home_source : Lookups.t -> State.Names.key -> State.source

val source_at :
  Lookups.t -> Path.t -> (State.source * Types.substitution * Infer.form_origin) option

val trait_substitution :
  Lookups.t -> Types.trait_reference -> Types.ty -> (Types.parameter * Types.argument) list

val part_of : ?inherited:bool -> Lookups.t -> Path.t -> State.source -> State.part option

val law_proofs :
  Lookups.t ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * (State.source * Types.substitution)) list

val impl_unfinished : Lookups.t -> State.Names.key -> bool
val law_unshown : Lookups.t -> Path.t -> Types.trait_reference -> Types.ty -> string -> bool
val function_contract : Lookups.t -> Path.t -> State.contract option
val trait_part : Lookups.t -> Path.t -> string -> Path.receiver -> State.part option
val capability_contract : Lookups.t -> Path.t -> string -> State.contract option
val capability_part : Lookups.t -> Path.t -> string -> State.part option

val method_contract :
  Lookups.t ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  Core.evidence ->
  State.contract option

val literal : Mir.formula -> Z.t option
val distinct_counters : 'a list -> 'a list
val resource_of : Mir.cost -> locals:Logic.term State.Locals.t -> Costs.resource option
val is_updating_helper : Lookups.t -> Path.t -> bool
val comparison : Core.comparison -> string option

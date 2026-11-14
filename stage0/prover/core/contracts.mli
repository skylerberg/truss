(** The contract of a callee: the clauses that its definition and its trait's state about it, read
    from the MIR. *)

val source_at_key : Query.context -> State.Names.key -> State.source option
(** The source of a definition, by its key. [None] for a definition with an error. *)

val source_at :
  Query.context -> Path.t -> (State.source * Types.substitution * Infer.form_origin) option
(** The source of the definition at a path, with the substitution its clauses are read under. A
    method that an [impl] inherits has its trait's default method's source, and a method that an
    [impl] derives has no text. *)

val trait_substitution :
  Query.context -> Types.trait_reference -> Types.ty -> (Types.parameter * Types.argument) list

val part_of : ?inherited:bool -> Query.context -> Path.t -> State.source -> State.part option

val law_proofs :
  Query.context ->
  Path.package ->
  Types.trait_reference ->
  Types.ty ->
  (string * (State.source * Types.substitution)) list

val impl_unfinished : Query.context -> State.Names.key -> bool
val law_unshown : Query.context -> Path.t -> Types.trait_reference -> Types.ty -> string -> bool

val function_contract :
  ?reading_package:Path.package -> Query.context -> Path.t -> State.contract option

val trait_part : Query.context -> Path.t -> string -> Path.receiver -> State.part option
val capability_contract : Query.context -> Path.t -> string -> State.contract option
val capability_part : Query.context -> Path.t -> string -> State.part option
val provided_body : Query.context -> Path.t -> string -> Path.receiver -> Mir.definition option

val method_contract :
  ?reading_package:Path.package ->
  Query.context ->
  Types.trait_reference ->
  string ->
  Path.receiver ->
  Core.evidence ->
  State.contract option

val literal : Mir.formula -> Z.t option
val distinct_counters : 'a list -> 'a list
val resource_of : Mir.cost -> locals:Logic.term State.Locals.t -> Costs.resource option
val is_test : State.context -> bool
val is_updating_helper : Query.context -> Path.t -> bool
val comparison : Core.comparison -> string option
val literal_bytes_limit : int

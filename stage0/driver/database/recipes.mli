val dependency_stages : Kind.stage list
val item_stages : Kind.stage list
val replace_builtin_entries : Tracker.t -> unit
val write_file : Tracker.t -> package:string -> Path.file -> string -> unit
val remove_file : Tracker.t -> Path.file -> unit
val forget_dependency : Tracker.t -> int -> unit
val list_linked : Tracker.t -> Profile.t -> roots:Lowered.Item.t list -> Store.linked list
val render_unit : Tracker.t -> Tracker.recorder -> Profile.t -> Lowered.Item.t -> string option
val list_definition_facts : unit -> Tracker.description list
val list_stale_units : Tracker.t -> Kind.stage -> scope:Store.scope -> int list

val drain_decide :
  Tracker.t -> ?on_bug:(Compiler_bug.t -> unit) -> scope:Store.scope -> Solver.t Lazy.t -> unit

val drain_stage :
  Tracker.t -> ?on_bug:(Compiler_bug.t -> unit) -> Kind.stage -> scope:Store.scope -> bool

val drain_claimed_items :
  Tracker.t -> ?on_bug:(Compiler_bug.t -> unit) -> string list option -> unit

val render_units : Tracker.t -> ?on_bug:(Compiler_bug.t -> unit) -> Profile.t -> int list -> unit
val make_evaluation_root : Prover.Obligation.evaluation -> Lowered.Item.t
val ensure_item : Tracker.t -> Lowered.Item.t -> unit
val supply_lowered : Tracker.t -> Lowered.Item.t -> Lowering.lowered -> unit
val record_evaluation : Tracker.t -> Lowered.Item.t -> Lowering.evaluation -> unit
val record_test_run : Tracker.t -> Lowered.Item.t -> Lowering.test_pass option -> unit

val list_runs :
  Tracker.t ->
  Tracker.recorder ->
  Prover.Lookups.t ->
  Prover.proof ->
  (Prover.Obligation.evaluation * Prover.Obligation.run) list

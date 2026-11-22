val package_stages : Kind.stage list
val forget_package : Tracker.t -> Path.package -> unit
val replace_builtin_entries : Tracker.t -> unit
val write_file : Tracker.t -> package:string -> Path.file -> string -> unit
val remove_file : Tracker.t -> Path.file -> unit
val forget_grant : Tracker.t -> int -> unit
val list_claimed_items : Tracker.t -> Path.package list option -> int list
val list_definition_facts : unit -> Tracker.description list
val list_stale_units : Tracker.t -> Kind.stage -> scope:Store.scope -> int list

val drain_decide :
  Tracker.t ->
  ?on_bug:(Compiler_bug.t -> unit) ->
  scope:Store.scope ->
  runs:(Prover.Obligation.evaluation * Prover.Obligation.run) list ->
  Solver.t Lazy.t ->
  unit

val drain_stage :
  Tracker.t -> ?on_bug:(Compiler_bug.t -> unit) -> Kind.stage -> scope:Store.scope -> bool

val make_evaluation_root : Prover.Obligation.evaluation -> Lowered.Item.t
val ensure_item : Tracker.t -> Lowered.Item.t -> unit

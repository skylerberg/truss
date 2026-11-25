val sort_in_dependency_order : Tracker.t -> Path.package list -> Path.package list
val make_names : Tracker.t -> Tracker.recorder -> Resolve.Names.lookups
val make_interface : Tracker.t -> Tracker.recorder -> is_checked:bool -> Interface.Lookups.t
val make_source : Tracker.t -> Tracker.recorder -> Resolve.Names.source
val make_infer : Tracker.t -> Tracker.recorder -> Infer.Lookups.t
val make_mir : Tracker.t -> Tracker.recorder -> Mir.lookups
val make_call_edges : Tracker.t -> Tracker.recorder -> Mir.Call_edges.lookups
val make_usage : Tracker.t -> Tracker.recorder -> Usage.Lookups.t
val make_package_checks : Tracker.t -> Tracker.recorder -> Package_checks.Lookups.t
val locate_items : Tracker.t -> Path.package
val is_worked_on : Tracker.t -> Path.package -> bool
val read_source : Tracker.t -> Tracker.recorder -> Path.file -> Source.t
val make_lowering : Tracker.t -> Tracker.recorder -> Lowering.Lookups.t
val make_proof : Tracker.t -> Tracker.recorder -> Prover.Lookups.t
val make_ownership : Tracker.t -> Tracker.recorder -> Ownership.Lookups.t

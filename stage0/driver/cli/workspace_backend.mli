val require_lowered_lookups : Database.t -> Path.package list -> Lowering.lowered_lookups
val create : Workspace.snapshot -> Lowering.lowered_lookups -> Backend.profile -> Backend.t

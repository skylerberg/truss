val require_lowered_lookups : Database.t -> Path.package list -> Backend.lowered_lookups
val create : Workspace.snapshot -> Backend.lowered_lookups -> Backend.profile -> Backend.t

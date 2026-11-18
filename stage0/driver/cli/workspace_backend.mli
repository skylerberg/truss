val require_lowered_lookups : Database.t -> Path.package list -> Backend.lowered_lookups
val create : Database.t -> Workspace.snapshot -> Path.package list -> Backend.profile -> Backend.t

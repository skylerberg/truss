val resolve_grant :
  Resolve.Names.lookups -> package:Path.package -> Grant.capability list -> Environment.grant

val describe_not_a_capability : dependency:Path.package -> Grant.capability -> string
val needs_grant : package:Path.package -> of_:Path.package -> bool

val list_missing :
  Lookups.t -> package:Path.package -> of_:Path.package -> Types.capability_set -> Path.t list

val describe_missing : subject:string -> of_:Path.package -> Path.t -> string

val list_evidence_uses :
  Lookups.t ->
  list_bounds:Impls.bounds ->
  Impls.evidence ->
  (Path.t * Types.impl_interface * Types.capability_set) list

val describe_missing_in_impls :
  Lookups.t ->
  package:Path.package ->
  (Path.t * Types.impl_interface * Types.capability_set) list ->
  string list

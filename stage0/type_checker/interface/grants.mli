val resolve_grant :
  Resolve.Names.lookups -> package:Path.package -> string list -> Environment.grant

val describe_not_a_capability : dependency:Path.package -> string -> string

val list_missing :
  Lookups.t -> package:Path.package -> of_:Path.package -> Types.capability_set -> Path.t list

val describe_missing : subject:string -> of_:Path.package -> Path.t -> string

val list_evidence_uses :
  Lookups.t ->
  bounds:Impls.bounds ->
  Impls.evidence ->
  (Path.t * Types.impl_interface * Types.capability_set) list

val describe_missing_in_impls :
  Lookups.t ->
  package:Path.package ->
  (Path.t * Types.impl_interface * Types.capability_set) list ->
  string list

val describe_missing_in_evidence :
  Lookups.t -> package:Path.package -> bounds:Impls.bounds -> Impls.evidence -> string list

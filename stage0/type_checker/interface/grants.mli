val resolve_grant :
  Resolve.Names.lookups -> package:Path.package -> Grant.capability list -> Environment.grant

val needs_grant : package:Path.package -> of_:Path.package -> bool

val list_missing :
  Lookups.t -> package:Path.package -> of_:Path.package -> Types.capability_set -> Path.t list

val list_evidence_uses :
  Lookups.t ->
  list_bounds:Impls.bounds ->
  Impls.solution ->
  (Path.t * Types.impl_interface * Types.capability_set) list

val list_missing_in_impls :
  Lookups.t ->
  package:Path.package ->
  (Path.t * Types.impl_interface * Types.capability_set) list ->
  (Types.impl_interface * Path.package * Path.t) list

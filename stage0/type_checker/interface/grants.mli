val grant : Lookups.t -> package:Path.package -> string list -> Environment.grant

val missing :
  Lookups.t -> package:Path.package -> of_:Path.package -> Types.capability_set -> Path.t list

val message : subject:string -> of_:Path.package -> Path.t -> string

val evidence_uses :
  Lookups.t ->
  bounds:Impls.bounds ->
  ?depth:int ->
  Impls.evidence ->
  (Path.t * Types.impl_interface * Types.capability_set) list

val messages :
  Lookups.t ->
  package:Path.package ->
  (Path.t * Types.impl_interface * Types.capability_set) list ->
  string list

val evidence_messages :
  Lookups.t -> package:Path.package -> bounds:Impls.bounds -> Impls.evidence -> string list

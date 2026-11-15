type grant = { capabilities : Path.t list; unknown : string list }

val granted : (Path.package * Path.package, grant option) Query.query

val missing :
  Query.context -> package:Path.package -> of_:Path.package -> Types.capability_set -> Path.t list

val message : subject:string -> of_:Path.package -> Path.t -> string

val evidence_uses :
  Query.context ->
  bounds:Impls.bounds ->
  ?depth:int ->
  Impls.evidence ->
  (Path.t * Types.impl_interface * Types.capability_set) list

val messages :
  Query.context ->
  package:Path.package ->
  (Path.t * Types.impl_interface * Types.capability_set) list ->
  string list

val evidence_messages :
  Query.context -> package:Path.package -> bounds:Impls.bounds -> Impls.evidence -> string list

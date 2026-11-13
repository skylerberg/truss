module Names = Resolve.Names

type edge = Calls of Path.t | Uses_impl of Path.t
type t = (Path.t * edge list) list

val traits_with_required : Query.context -> Path.t -> Path.t list
val package_impls : (Path.package, (Path.t * Path.t * Path.t option * Path.t list) list) Query.query
val impls_for : ('a * Path.t * Path.t option * 'b) list -> Path.t list -> Types.ty -> 'a list

val impls_used :
  Query.context -> ('a * Path.t * Path.t option * 'b) list -> 'c Core.target -> 'a list

val dispatched : 'a Core.target -> bool
val impl_methods : Query.context -> Path.t -> Path.t list
val reaches : Query.context -> package:Path.package -> from:Path.t -> target:Path.t -> bool
val recursive : Query.context -> package:Path.package -> Path.t -> bool

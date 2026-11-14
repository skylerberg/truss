val bound_diagnostics :
  Query.context ->
  package:Path.package ->
  bounds:Impls.bounds ->
  (Syntax.span * Types.ty) list ->
  Syntax.diagnostic list
(** The bounds that the arguments of each written type must satisfy. Each failure is a diagnostic:
    the bound does not hold, or the [impl] that satisfies it uses a capability that its package is
    not granted. The types that the annotations in a body write are checked in the same way. *)

val diagnostics : (Resolve.Names.key, Syntax.diagnostic list) Query.query
val reported : Query.context -> Path.t -> Diagnostic.reported option

(** Checking each definition's outward-facing part.

    These checks read other definitions' interfaces, such as the [impl]s that decide whether a bound
    holds, so they run apart from lowering: an interface never waits on a check of itself. *)

val bound_diagnostics :
  Query.context ->
  package:Path.package ->
  bounds:Impls.bounds ->
  (Syntax.span * Types.ty) list ->
  Diagnostic.t list
(** The bounds that the arguments of each written type must satisfy. Each failure is a diagnostic:
    the bound does not hold, or the [impl] that satisfies it uses a capability that its package is
    not granted. The types that the annotations in a body write are checked in the same way. *)

val diagnostics : (Resolve.Names.key, Diagnostic.t list) Query.query

val reported : Query.context -> Path.t -> Diagnostic.reported option
(** The report of a definition whose interface has an error, for a use of it that the error leaves
    nothing to check against. *)

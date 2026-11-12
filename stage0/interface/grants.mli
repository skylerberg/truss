(** The capabilities that a package's manifest grants to each dependency, and the capabilities that
    a dependency's code uses beyond its grant. A grant is checked wherever the dependency's code is
    referenced: at a call, at a function value, and where an [impl] of the dependency satisfies a
    bound. *)

type grant = {
  capabilities : Path.t list;
  unknown : string list;  (** The entries that name no capability *)
}

val granted : (string * string, grant option) Query.query
(** The capabilities that a package's manifest grants to a dependency, or [None] for a package that
    the manifest does not list. *)

val missing : Query.context -> package:string -> of_:string -> Types.capability list -> Path.t list
(** The capabilities that some code of the package [of_] uses and that [package]'s manifest does not
    grant to it. A package's own code and the standard library need no grant. A capability parameter
    is instantiated by the caller with the caller's own capabilities, so it needs none either. *)

val message : what:string -> of_:string -> Path.t -> string
(** The sentence for a capability that is not granted. *)

val evidence_uses :
  Query.context ->
  bounds:Impls.bounds ->
  ?depth:int ->
  Impls.evidence ->
  (Path.t * Types.impl_interface * Types.capability list) list
(** The capabilities that the [impl]s satisfying a bound can use: the resolved [impl] and,
    recursively, the [impl]s that satisfy its own bounds, each with the capabilities of its methods.
*)

val messages :
  Query.context ->
  package:string ->
  (Path.t * Types.impl_interface * Types.capability list) list ->
  string list
(** The diagnostic messages for the capabilities that such [impl]s use without a grant, in code of
    [package]. *)

val evidence_messages :
  Query.context -> package:string -> bounds:Impls.bounds -> Impls.evidence -> string list

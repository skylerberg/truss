(** Whether a release of a package is compatible with the previous release, by comparing the two
    releases' public definitions. *)

type change =
  | Breaks of string  (** A guarantee of the previous release that this release removes *)
  | Grows of string  (** An addition that the previous release lacked *)

type public_change = { path : Path.t; change : change }
(** A change to a public definition, described by a predicate that completes a sentence about the
    definition. *)

val compare :
  before:Query.context -> after:Query.context -> Path.package -> public_change list * bool
(** The changes to a package's public definitions between two states, each holding the package and
    its dependencies, and whether the package ran on every target and now requires 64-bit targets,
    which is incompatible for every user on other targets.

    A signature's types are compared after type checking. A contract is compared syntactically: a
    release may remove a [requires] clause and add an [ensures] or cost clause, and any other change
    to a contract is incompatible. A yielding method that could be pulled as a cursor and no longer
    can is incompatible too, although that property is inferred from its body. *)

val breaks : public_change list -> (Path.t * string) list
val grows : public_change list -> (Path.t * string) list

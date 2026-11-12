(** Whether a release of a package is compatible with the release before it, read from the two
    releases' public definitions. *)

type change =
  | Breaks of string  (** A guarantee of the release before that this one drops *)
  | Grows of string  (** An addition to the public API of the release before *)

type public_change = { path : Path.t; change : change }
(** A change to a public definition, described as the end of a sentence about it. *)

val compare :
  before:Query.context -> after:Query.context -> Path.package -> public_change list * bool
(** The changes to a package's public definitions from one state to another, each state holding the
    package and the packages it uses, and whether the package ran on every target and now runs only
    on 64-bit ones, which breaks every user that runs on the others.

    A signature's types are compared as the checker inferred them. A contract is compared as it is
    written: a release may drop a [requires] clause and add an [ensures] or a cost clause, and any
    other difference in one breaks. A yielding method that could be pulled as a cursor and no longer
    can breaks too, though that is inferred from its body. *)

val breaks : public_change list -> (Path.t * string) list
val grows : public_change list -> (Path.t * string) list

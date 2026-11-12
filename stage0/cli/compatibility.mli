(** Whether a release of a package keeps what the release before it offered, read from the two
    releases' public definitions. *)

type change =
  | Breaks of string  (** What a user of the release before could rely on and no longer can *)
  | Grows of string  (** What the release offers that the one before did not *)

type found = { path : Path.t; change : change }
(** A change to a public definition, with what changed as the end of a sentence about it. *)

val compare : before:Query.context -> after:Query.context -> Path.package -> found list * bool
(** What a package's public definitions change from one state to another, each state holding the
    package and the packages it uses, and whether the package ran on every target and now runs only
    on 64-bit ones, which breaks every user that runs on the others.

    A signature's types are compared as the checker worked them out. A contract is compared as it is
    written: a release may drop a [requires] clause and add an [ensures] or a cost clause, and any
    other difference in one breaks. A yielding method that could be pulled as a cursor and no longer
    can breaks too, though that is worked out from its body. *)

val breaks : found list -> (Path.t * string) list
val grows : found list -> (Path.t * string) list

(** A published package's version: three numbers, as [1.4.2]. *)

type t = int * int * int

val parse : string -> t option
val show : t -> string
val compare : t -> t -> int

val major_of_name : string -> int
(** The first number of every version of a package: the number after [_v] at the end of its name, as
    2 for [acme::geometry_v2], or 1 for a name without one. *)

val first : string -> t
(** A package's first version, by its name: [1.0.0], or [2.0.0] for a name that ends in [_v2]. *)

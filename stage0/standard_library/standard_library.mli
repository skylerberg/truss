(** The standard library's source, which ships inside the compiler. *)

val manifest : string
(** The text of the [standard] package's manifest, [standard/truss.toml]. *)

val modules : (Path.module_ * string) list
(** Each module of the [standard] package, with its text. *)

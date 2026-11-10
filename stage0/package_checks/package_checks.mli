(** The checks that look at more than one definition of a package. *)

type placed = { module_ : Path.module_; diagnostic : Diagnostic.t }
(** A diagnostic in the file of the module that holds it, in that file's offsets. *)

val check : (string, placed list) Query.query
(** A package's errors, by its name. *)

val diagnostics : Query.context -> Path.module_ -> Diagnostic.t list
(** The package's errors in one file, in order. *)

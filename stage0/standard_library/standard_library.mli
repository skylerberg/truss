(** The standard library's source, which ships inside the compiler. See TYPECHECKER.md, "The
    prelude". *)

val package : string

val modules : (Path.module_ * string) list
(** Each module of the [standard] package, with its text. *)

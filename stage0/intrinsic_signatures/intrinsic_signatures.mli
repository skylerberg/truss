(** The signatures of [standard::intrinsic]'s operations, as data the type checker and code
    generation both read. See CODEGEN.md, "The system interface". *)

val signature : Intrinsic.operation -> Types.signature
(** Each generic parameter is owned by the operation's path. *)

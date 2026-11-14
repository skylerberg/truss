type problem = { code : Diagnostic.Code.lexer; message : string; start : int; stop : int }
(** A problem in a literal, at offsets within it. *)

type checked = { value : Token.kind; problem : problem option; fixes : (string * string) list }
(** A literal's value, its first problem, and the fixes for the whole literal, each a title and a
    replacement. *)

val is_radix_prefix : string -> int -> bool
(** Whether `0x`, `0b`, or `0o` starts at the offset. *)

val name_end : string -> int -> int
(** The end of the name characters from the offset. *)

val scan_end : string -> int -> int
(** The end of the number that starts at the offset. *)

val check : string -> checked
(** A literal, checked against Truss's grammar for numbers. *)

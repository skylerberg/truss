(** Prints a syntax tree as a compact S-expression, for tests and for [stage0/tools/debug]. Spans,
    blank lines, and how literals were written are left out, so the output shows only the tree's
    structure. Names and literals print as written in Truss, and every other node as a parenthesized
    form named by its keyword or operator, such as [(+ a (- b c))]. *)

val path : Syntax.path -> string
val expression : Syntax.expression -> string
val clause : Syntax.clause -> string
val law : Syntax.law -> string
val statement : Syntax.statement -> string

val definition : ?methods:string list -> Syntax.definition -> string
(** A definition. [methods] are the methods written inside a trait, an [impl], or a capability,
    already printed, which come after its own members. *)

val definitions : Syntax.definition Syntax.item list -> string list
(** A file's definitions, with each method inside the one it is written inside. *)

val file : Syntax.file -> string

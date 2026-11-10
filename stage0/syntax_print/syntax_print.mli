(** Prints a syntax tree as a compact S-expression, for tests and for [stage0/tools/debug]. Spans,
    blank lines, and how literals were written are left out, so the output shows what a tree says.
    Names and literals print as written in Truss, and every other node as a parenthesized form named
    by its keyword or operator, such as [(+ a (- b c))]. *)

val path : Syntax.path -> string
val expression : Syntax.expression -> string
val clause : Syntax.clause -> string
val law : Syntax.law -> string
val statement : Syntax.statement -> string
val pattern : Syntax.pattern -> string
val type_expression : Syntax.type_expression -> string
val definition : Syntax.definition -> string
val file : Syntax.file -> string

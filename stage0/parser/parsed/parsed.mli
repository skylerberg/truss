type t = { file : Syntax.file; diagnostics : Diagnostic.t list; text : string }

val parse : Source.t -> t

type file = { file : Syntax.file; diagnostics : Diagnostic.t list; text : string }

val parse : Source.t -> file

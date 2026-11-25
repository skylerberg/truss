type t = Lexing of Lexing.t | Parsing of Parsing.t

val locate : t -> Source.span
val describe : t -> Source.span Description.t
val render : text:string -> t -> Diagnostic.t

val path : Syntax.path -> string
val expression : Syntax.expression -> string
val clause : Syntax.clause -> string
val law : Syntax.law -> string
val file : Syntax.file -> string

module For_testing : sig
  val statement : Syntax.statement -> string
  val definition : ?methods:string list -> Syntax.definition -> string
  val definitions : Syntax.top_level list -> string list
end

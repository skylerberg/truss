val document : string -> string
val source : string -> Source.t
val parse : string -> Syntax.file * Diagnostic.t list
val items : Syntax.file -> Syntax.definition Syntax.item list
val codes : Diagnostic.t list -> string list
val no_diagnostics : string -> Diagnostic.t list -> unit
val definitions : string -> string list -> unit
val definition : string -> string -> unit
val body_of : string -> Syntax.statement list * Diagnostic.t list
val statements : string -> string list -> unit
val statement : string -> string -> unit
val recovered_definitions : ?codes:string list -> string -> string list -> unit
val recovered_statements : ?codes:string list -> string -> string list -> unit

val error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit

val body_error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit

val read_document : string -> string
val make_source : string -> Source.t
val parse : string -> Syntax.file * Diagnostic.t list
val list_items : Syntax.file -> Syntax.definition Syntax.item list
val expect_no_diagnostics : string -> Diagnostic.t list -> unit
val expect_definitions : string -> string list -> unit
val expect_definition : string -> string -> unit
val parse_body : string -> Syntax.statement list * Diagnostic.t list
val expect_statements : string -> string list -> unit
val expect_statement : string -> string -> unit
val expect_recovered_definitions : ?codes:string list -> string -> string list -> unit
val expect_recovered_statements : ?codes:string list -> string -> string list -> unit

val expect_error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit

val expect_body_error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit

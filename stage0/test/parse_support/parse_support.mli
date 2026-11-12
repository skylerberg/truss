(** Helpers for the parser's tests: parsing a text, and asserting its result, a tree, statements, or
    one diagnostic with its fixes. *)

val document : string -> string
(** The text of a document of the repository, by its name. *)

val source : string -> Source.t
val parse : string -> Syntax.file * Diagnostic.t list
val codes : Diagnostic.t list -> string list
val no_diagnostics : string -> Diagnostic.t list -> unit

val definitions : string -> string list -> unit
(** Asserts that a text parses with no diagnostics into definitions that print as the expected
    strings. *)

val definition : string -> string -> unit

val body_of : string -> Syntax.statement list * Diagnostic.t list
(** The statements of a function whose body is the text. *)

val statements : string -> string list -> unit
(** Asserts that a text, as the body of a function, parses with no diagnostics into statements that
    print as the expected strings. *)

val statement : string -> string -> unit

val error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit
(** Asserts that a text gives exactly one diagnostic, with [code], starting at the [occurrence]th
    occurrence of [at]. With [fixed], its fixes must turn the text into [fixed] and then
    [alternatives], each of which must parse with no diagnostics. Without [fixed], it must have no
    fix. *)

val body_error :
  ?fixed:string ->
  ?alternatives:string list ->
  ?occurrence:int ->
  string ->
  code:Diagnostic.Code.parser ->
  at:string ->
  unit
(** As {!error}, for a text that is the body of a function. *)

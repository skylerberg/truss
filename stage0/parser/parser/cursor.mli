exception Failed

type t

val create :
  text:string ->
  diagnostics:Diagnostic.Collector.t ->
  base:int ->
  Token.t array ->
  first:int ->
  stop:int ->
  t

val sub_cursor : t -> Token.t array -> t
val interpolation : t -> Token.interpolation -> t
val restarted : t -> t
val index : t -> int
val fresh_id : t -> int
val token_at : t -> int -> Token.t
val peek : t -> Token.t
val peek_kind : t -> Token.kind
val peek_ahead : t -> int -> Token.kind
val advance : t -> unit
val next : t -> Token.t
val at_end : t -> bool
val is : t -> Token.kind -> bool
val is_punctuation : t -> Token.punctuation -> bool
val is_keyword : t -> Token.keyword -> bool
val accept_punctuation : t -> Token.punctuation -> bool
val accept_keyword : t -> Token.keyword -> bool
val span : t -> Source.span -> Syntax.Span.t
val previous_token : t -> Token.t option
val previous_stop : t -> int
val span_from : t -> int -> Syntax.Span.t
val absolute : t -> Syntax.span -> Source.span
val text : t -> Source.span -> string

val report :
  t ->
  ?notes:(Diagnostic.span * string) list ->
  ?fixes:Diagnostic.span Diagnostic.fix list ->
  Diagnostic.Code.parser ->
  Diagnostic.span ->
  string ->
  unit

val fail : t -> string -> 'a
val expect_punctuation : t -> Token.punctuation -> unit
val expect_keyword : t -> Token.keyword -> unit
val nested : t -> (t -> 'a) -> 'a
val check_chain_length : t -> chain_length:int -> unit
val closer : t -> int -> int
val skip_to : t -> int -> unit
val skip_one : t -> unit
val group : t -> Token.t array
val skip_method : t -> unit
val skip_trailing_comma : t -> unit
val is_after_inserted_closer : t -> bool
val bracketed : t -> item:(t -> 'a) -> recover:(Syntax.Span.t -> 'a) -> 'a list
val lines : t -> item:(t -> 'a) -> recover:(int -> Syntax.Span.t -> 'a) -> 'a list
val blank_line_before : t -> int -> bool
val recovered : t -> Syntax.span list
val methods : t -> Split.piece list

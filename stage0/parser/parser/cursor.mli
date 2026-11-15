exception Failed

type t

val create :
  diagnostics:Diagnostic.Collector.t -> base:int -> Token.t array -> first:int -> stop:int -> t

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
val span : t -> Source.span -> Source.Definition_span.t
val previous_token : t -> Token.t option
val previous_stop : t -> int
val span_from : t -> int -> Source.Definition_span.t
val absolute : t -> Source.Definition_span.t -> Source.span
val spelling : t -> ?insertions:(int * string) list -> Source.span -> string option
val recovers : Diagnostic.Code.parser -> bool

val report :
  t ->
  ?notes:(Source.span * string) list ->
  ?fixes:Source.span Diagnostic.fix list ->
  Diagnostic.Code.parser ->
  Source.span ->
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
val bracketed : t -> item:(t -> 'a) -> recover:(Source.Definition_span.t -> 'a) -> 'a list
val lines : t -> item:(t -> 'a) -> recover:(int -> Source.Definition_span.t -> 'a) -> 'a list
val blank_line_before : t -> int -> bool
val recovered : t -> Source.Definition_span.t list
val methods : t -> Split.piece list

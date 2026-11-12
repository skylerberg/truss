exception Failed

type t = {
  tokens : Token.t array;
  first : int;
  stop : int;
  base : int;
  closers : int array;
  text : string;
  diagnostics : Diagnostic.Collector.t;
  mutable index : int;
  mutable depth : int;
  next_id : int ref;
  recoveries : Source.span list ref;
  methods : (int * int) list ref;
  mutable after_inserted_closer : bool;
  mutable unterminated : bool;
  mutable line_ended : bool;
}

val create :
  text:string ->
  diagnostics:Diagnostic.Collector.t ->
  base:int ->
  Token.t array ->
  first:int ->
  stop:int ->
  t

val over : ?stop:int -> t -> Token.t array -> t
val restarted : t -> t
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
val relative : t -> int -> int
val span : t -> Source.span -> Syntax.Span.t
val previous_stop : t -> int
val span_from : t -> int -> Syntax.Span.t
val absolute : t -> Syntax.span -> Source.span
val text : t -> Source.span -> string

val report :
  t ->
  ?notes:(Diagnostic.span * string) list ->
  ?fixes:Diagnostic.fix list ->
  Diagnostic.Code.parser ->
  Diagnostic.span ->
  string ->
  unit

val fail : t -> string -> 'a
val expect_punctuation : t -> Token.punctuation -> unit
val expect_keyword : t -> Token.keyword -> unit
val nested : t -> (t -> 'a) -> 'a
val check_chain_length : t -> length:int -> unit
val closer : t -> int -> int
val skip_to : t -> int -> unit
val skip_one : t -> unit
val bracketed : t -> item:(t -> 'a) -> recover:(Syntax.Span.t -> 'a) -> 'a list
val lines : t -> item:(t -> 'a) -> recover:(int -> Syntax.Span.t -> 'a) -> 'a list
val blank_line_before : t -> int -> bool

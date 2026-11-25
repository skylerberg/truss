exception Failed

type t

val create :
  diagnostics:Syntax_catalog.Parsing.t Dynarray.t ->
  base:int ->
  Token.t array ->
  first:int ->
  stop:int ->
  t

val enter_interpolation : t -> Token.interpolation -> t
val index : t -> int
val lookup_token : t -> int -> Token.t
val peek : t -> Token.t
val peek_kind : t -> Token.kind
val peek_ahead : t -> int -> Token.kind
val advance : t -> unit
val take : t -> Token.t
val is_at_end : t -> bool
val is : t -> Token.kind -> bool
val is_punctuation : t -> Token.punctuation -> bool
val is_keyword : t -> Token.keyword -> bool
val accept_punctuation : t -> Token.punctuation -> bool
val accept_keyword : t -> Token.keyword -> bool
val make_definition_span : t -> Source.span -> Source.Definition_span.t
val find_previous_token : t -> Token.t option
val compute_previous_stop : t -> int
val allocate_id : t -> Source.Definition_span.t -> Syntax.id
val allocate_id_from : t -> int -> Syntax.id
val read_span : t -> Syntax.id -> Source.Definition_span.t
val set_span : t -> Syntax.id -> Source.Definition_span.t -> unit
val read_file_span : t -> Syntax.id -> Source.span
val make_file_span : t -> Source.Definition_span.t -> Source.span
val spell : t -> ?insertions:(int * string) list -> Source.span -> string option
val joins_neighbors : t -> Source.span -> string -> bool
val has_reported : t -> bool

val report :
  t ->
  ?fixes:Syntax_catalog.Parsing.fix list ->
  Source.span ->
  Syntax_catalog.Parsing.problem ->
  unit

val fail : t -> Syntax_catalog.Parsing.expected -> 'a
val expect_punctuation : t -> Token.punctuation -> unit
val expect_keyword : t -> Token.keyword -> unit
val run_nested : t -> (t -> 'a) -> 'a
val check_chain_length : t -> chain_length:int -> unit
val lookup_closer : t -> int -> int
val find_angle_closer : t -> int option
val skip_to : t -> int -> unit
val skip_one : t -> unit
val group : t -> Token.t array
val parse_separated : t -> separator:Token.punctuation -> (t -> 'a) -> 'a list
val skip_piece : t -> Split.piece
val is_after_inserted_closer : t -> bool

val parse_bracketed :
  t -> parse_item:(t -> 'a) -> recover:(Source.Definition_span.t -> 'a) -> 'a list

val parse_lines : t -> parse_item:(t -> 'a) -> recover:(Source.Definition_span.t -> 'a) -> 'a list
val collect_positions : t -> Syntax.positions

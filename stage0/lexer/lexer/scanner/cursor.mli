type t = {
  source : Source.t;
  text : string;
  length : int;
  diagnostics : Diagnostic.Collector.t;
  mutable position : int;
  mutable first_line_break : Source.span option;
  mutable blank_line : bool;
  mutable line_is_blank : bool;
  mutable unterminated_at_end : bool;
  names : (string, Names.checked) Hashtbl.t;
}

val create : Source.t -> Diagnostic.Collector.t -> t

type ending = Closed | Unterminated
type item = Token of { kind : Token.kind; start : int; ending : ending } | Line_end | End

val span : int -> int -> Source.span
val byte : t -> int -> int

val report :
  t ->
  ?notes:(Diagnostic.span * string) list ->
  ?fixes:Diagnostic.fix list ->
  code:Diagnostic.Code.lexer ->
  Diagnostic.span ->
  string ->
  unit

val is_line_break : int -> bool
val is_end_of_line : int -> bool
val is_space : int -> bool
val is_digit : int -> bool
val is_hexadecimal_digit : int -> bool
val is_ascii_letter : int -> bool
val is_ascii_name_byte : int -> bool
val quote : int
val dollar : int
val decode : t -> int -> int
val run_length : t -> int -> int -> int
val skip_spaces : t -> int -> int
val end_of_line : t -> int -> int
val line_break_length : t -> int -> int
val indentation : t -> int -> string
val spaces_before : t -> int -> int
val only_spaces_before : t -> int -> bool
val describe_code_point : int -> string
val show_character : t -> int -> string

type ending = Closed | Unterminated

type token = {
  kind : Token.kind;
  start : int;
  stop : int;
  ending : ending;
  first_line_break : Source.span option;
  blank_line : bool;
}

type item = Token of token | Line_end | End

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
  mutable previous : token option;
  mutable held : item list;
  mutable semicolons : int list;
  foreign_escape : t -> Buffer.t -> bool;
}

val create : foreign_escape:(t -> Buffer.t -> bool) -> Source.t -> Diagnostic.Collector.t -> t
val is_at_end : t -> int -> bool
val lookup_char : t -> int -> char
val is_at : t -> int -> char -> bool
val satisfies : t -> int -> (char -> bool) -> bool

val report :
  t ->
  ?notes:(Source.span * string) list ->
  ?fixes:Source.span Diagnostic.fix list ->
  code:Diagnostic.Code.lexer ->
  Source.span ->
  string ->
  unit

val is_line_break : char -> bool
val is_end_of_line : t -> int -> bool
val is_space : char -> bool
val is_digit : char -> bool
val is_hexadecimal_digit : char -> bool
val is_ascii_letter : char -> bool
val is_ascii_name_byte : char -> bool
val is_ascii : char -> bool
val list_code_fixes : t -> Source.span -> string list -> Source.span Diagnostic.fix list
val decode : t -> int -> Unicode.Decoded.t
val run_length : t -> int -> char -> int
val skip_spaces : t -> int -> int
val compute_end_of_line : t -> int -> int
val measure_line_break : t -> int -> int
val extract_indentation : t -> int -> string
val count_spaces_before : t -> int -> int
val has_only_spaces_before : t -> int -> bool
val describe_code_point : int -> string
val show_character : t -> int -> string

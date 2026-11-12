type problem = { code : Diagnostic.Code.lexer; message : string; start : int; stop : int }
type checked = { value : Token.kind; problem : problem option; fixes : (string * string) list }

val is_radix_prefix : string -> int -> bool
val scan_end : string -> int -> int

type issue = { problem : problem; fixable : bool }
type group = { group : string; offset : int }
type exponent = { marker : char; marker_offset : int; sign : string; exponent_digits : group }

type decimal = {
  whole : group;
  fraction : group option;
  exponent : exponent option;
  rest_offset : int;
}

val check : string -> checked
val float_with_zero : string -> Token.kind option

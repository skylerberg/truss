type problem = { code : Diagnostic.Code.lexer; message : string; start : int; stop : int }
type checked = { value : Token.kind; problem : problem option; fixes : (string * string) list }

val name_end : string -> int -> int
val scan_end : string -> int -> int
val check : string -> checked

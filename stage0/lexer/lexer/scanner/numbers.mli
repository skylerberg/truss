type problem = { problem : Syntax_catalog.Lexing.number_problem; start : int; stop : int }
type fix = { replacement : string; reading : Syntax_catalog.Lexing.reading option }
type checked = { value : Token.kind; problem : problem option; fixes : fix list }

val compute_name_end : string -> int -> int
val scan_end : string -> int -> int
val check : string -> checked
val remove_underscores : string -> string

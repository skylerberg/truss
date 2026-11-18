type linkage = External | Internal
type failure = Echo | Todo

val raise_bug : ('a, unit, string, 'b) format4 -> 'a
val render_site_symbol : Lowered.site -> string
val site_struct : string
val render_integer_type : Memory_layout.integer -> string
val render_unsigned_type : Memory_layout.integer -> string
val is_signed : Memory_layout.integer -> bool
val runtime_declarations : string
val helpers : (string * string) list

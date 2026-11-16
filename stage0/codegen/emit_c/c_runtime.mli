type build = Development | Release
type linkage = External | Internal
type failure = Echo | Todo

val bug : ('a, unit, string, 'b) format4 -> 'a
val site_symbol : Lowered.site -> string
val site_struct : string
val integer_c : Memory_layout.integer -> string
val unsigned_c : Memory_layout.integer -> string
val signed : Memory_layout.integer -> bool
val runtime_declarations : string
val helpers : (string * string) list

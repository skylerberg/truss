type build = Development | Release
type linkage = External | Internal

val bug : ('a, unit, string, 'b) format4 -> 'a
val anchor_symbol : Path.t -> string
val anchor_struct : string
val integer_c : Memory_layout.integer -> string
val unsigned_c : Memory_layout.integer -> string
val signed : Memory_layout.integer -> bool
val runtime_declarations : Memory_layout.target -> string
val helpers : (string * string) list

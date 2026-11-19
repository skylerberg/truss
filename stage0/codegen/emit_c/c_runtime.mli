type linkage = External | Internal
type failure = Echo | Todo

type helper =
  | Lend
  | Compare_bytes
  | Float64_bits
  | Float32_bits
  | Float64_from_bits
  | Float32_from_bits

val raise_bug : ('a, unit, string, 'b) format4 -> 'a
val render_site_symbol : Lowered.site -> string
val render_capability_symbol : Path.t -> string
val shared_structs : string
val render_integer_type : Memory_layout.integer -> string
val render_unsigned_type : Memory_layout.integer -> string
val is_signed : Memory_layout.integer -> bool
val runtime_declarations : string
val render_helper_name : helper -> string
val helpers : (helper * string) list

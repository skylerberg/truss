type t
type changes = Changed of string list | Overflow

val start : is_skipped_name:(string -> bool) -> cookie_directory:string -> string -> t
val extract_descriptor : t -> Unix.file_descr
val read_changes : t -> changes
val stop : t -> unit

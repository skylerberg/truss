type t
type changes = Changed of string list | Overflow

val start : skipped:(string -> bool) -> cookie_directory:string -> string -> t
val descriptor : t -> Unix.file_descr
val changes : t -> changes
val stop : t -> unit

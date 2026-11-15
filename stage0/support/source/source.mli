type span = private { start : int; stop : int }

val span : int -> int -> span
val zero_width : int -> span

type t

val create : path:string -> string -> t
val read_file : string -> t
val path : t -> string
val text : t -> string
val position : t -> int -> int * int

type units = Bytes | Scalar_values | Utf_16_code_units

val location : units -> t -> int -> int * int
val offset : units -> t -> line:int -> column:int -> int
val line_start : t -> int -> int
val fragment_line_start : string -> int -> int
val line_end : t -> int -> int
val starts_line : t -> int -> bool

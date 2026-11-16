val read_lines : string -> string -> string list
val read_records : string -> string -> string list list
val parse_code_point : string -> int
val parse_code_point_range : string -> int * int
val merge : (int * int) list -> (int * int) list

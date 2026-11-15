type anchor = { definition : Path.t; path : string; first_line : int }

val anchors_file : anchor list -> string

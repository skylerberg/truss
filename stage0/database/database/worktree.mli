type stamp = { size : int; modified : float; inode : int }

val skipped : string -> bool
val files : string -> (string * stamp) list

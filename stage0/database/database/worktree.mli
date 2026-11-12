type stamp = { size : int; modified : float; inode : int }

val skipped : string -> bool
val files : string -> (string * stamp) list
val parent : string -> string
val segments : string -> string list
val owner : string list -> string -> string option

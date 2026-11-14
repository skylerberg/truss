type t = { list : unit -> (string * string) list; read : string -> string option }

val of_directory : string -> t
val of_texts : (string * string) list -> t
val of_commit : directory:string -> string -> t option
val with_changes : t -> (string * string option) list -> t

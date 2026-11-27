val run :
  ?input:string -> ?on_output:(string -> unit) -> string -> string list -> int * string * string

val run_attached : string -> string list -> int

type coprocess

val start : string -> string list -> coprocess
val converse : coprocess -> string -> until:string -> (string, string) result
val stop : coprocess -> unit

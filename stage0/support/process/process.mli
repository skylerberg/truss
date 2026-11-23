val run :
  ?input:string -> ?on_output:(string -> unit) -> string -> string list -> int * string * string

val run_attached : string -> string list -> int

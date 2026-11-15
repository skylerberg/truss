val run :
  ?environment:(string * string) list ->
  ?input:string ->
  ?on_output:(string -> unit) ->
  string ->
  string list ->
  int * string * string

val run_with_time_limit :
  ?environment:(string * string) list ->
  ?input:string ->
  ?on_output:(string -> unit) ->
  time_limit_ms:int ->
  string ->
  string list ->
  (int * string * string) option

val run_attached : string -> string list -> int

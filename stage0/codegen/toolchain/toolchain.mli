type t = { compiler : string; identity : string }

val find : unit -> (t, string) result
val added_flags_variable : string
val split_flags : string -> string list
val required_flags : string list

type optimization = O1 | O2

val link_time_optimization : t -> string list
val optimization_flag : optimization -> string

val compile :
  t ->
  optimization:optimization ->
  ?extra:string list ->
  source:string ->
  output:string ->
  unit ->
  (unit, string) result

val link :
  t -> ?extra:string list -> objects:string list -> output:string -> unit -> (string, string) result

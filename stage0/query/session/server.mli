val running : string -> bool
val serving : unit -> string list

type 'response message = Progress of string | Final of 'response

val stop : unit -> unit

val serve :
  key:string ->
  alive:(unit -> bool) ->
  idle:(unit -> unit) ->
  keep:(unit -> (string * string) list) ->
  handle:(progress:(string -> unit) -> 'a -> 'b) ->
  unit

val store_directory : unit -> string

val call :
  ?program:string ->
  ?start_server:bool ->
  key:string ->
  progress:(string -> unit) ->
  'a ->
  ('b, string) result

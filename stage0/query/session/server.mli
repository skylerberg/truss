val running : string -> bool
val serving : unit -> string list

type 'response message = Progress of string | Final of 'response

val stop : unit -> unit
val listen : key:string -> (Unix.file_descr, string) result

val serve :
  key:string ->
  ?socket:Unix.file_descr ->
  alive:(unit -> bool) ->
  idle:(unit -> unit) ->
  answered:(unit -> unit) ->
  keep:(unit -> (string * string) list) ->
  handle:(progress:(string -> unit) -> 'a -> 'b) ->
  unit ->
  unit

val store_directory : unit -> string

val call :
  ?program:string ->
  ?start_server:bool ->
  key:string ->
  progress:(string -> unit) ->
  'a ->
  ('b, string) result

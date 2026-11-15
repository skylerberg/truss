val serving : unit -> string list
val stop : unit -> unit

val serve :
  key:string ->
  alive:(unit -> bool) ->
  collect:(unit -> unit) ->
  watched:(unit -> Unix.file_descr list) ->
  changed:(Unix.file_descr -> unit) ->
  handle:(progress:(string -> unit) -> 'a -> 'b) ->
  unit

val call :
  ?program:string ->
  ?start_server:bool ->
  key:string ->
  progress:(string -> unit) ->
  'a ->
  ('b, string) result

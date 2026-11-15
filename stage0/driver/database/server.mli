val serving : unit -> string list
val stop : unit -> unit
val wait_until_ended : key:string -> unit
val listen : key:string -> (Unix.file_descr, string) result

val serve :
  key:string ->
  alive:(unit -> bool) ->
  collect:(unit -> unit) ->
  watched:(unit -> Unix.file_descr list) ->
  changed:(Unix.file_descr -> unit) ->
  handle:(progress:(string -> unit) -> 'a -> 'b) ->
  answered:(unit -> unit) ->
  close:(unit -> unit) ->
  unit

val call :
  ?program:string ->
  ?start_server:bool ->
  key:string ->
  progress:(string -> unit) ->
  'a ->
  ('b, string) result

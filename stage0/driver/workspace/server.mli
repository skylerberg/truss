val serving : unit -> string list
val stop : unit -> unit
val wait_until_ended : key:string -> unit
val listen : key:string -> (Unix.file_descr, string) result

val serve :
  key:string ->
  is_alive:(unit -> bool) ->
  collect:(unit -> unit) ->
  watcher_descriptors:(unit -> Unix.file_descr list) ->
  propagate:(Unix.file_descr -> unit) ->
  handle:(progress:(string -> unit) -> 'a -> 'b) ->
  save:(unit -> unit) ->
  close:(unit -> unit) ->
  unit

val call :
  ?start_server:bool -> key:string -> progress:(string -> unit) -> 'a -> ('b, string) result

module For_testing : sig
  val call :
    program:string ->
    ?start_server:bool ->
    key:string ->
    progress:(string -> unit) ->
    'a ->
    ('b, string) result
end

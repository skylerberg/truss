val list_servers : unit -> string list
val stop_servers : ?key:string -> wait:bool -> unit -> bool
val listen : key:string -> (Unix.file_descr, string) result

val serve :
  key:string ->
  is_alive:(unit -> bool) ->
  collect:(unit -> unit) ->
  list_watcher_descriptors:(unit -> Unix.file_descr list) ->
  propagate:(Unix.file_descr -> unit) ->
  handle:(report_progress:(string -> unit) -> 'a -> 'b) ->
  save:(unit -> unit) ->
  close:(unit -> unit) ->
  unit

val call :
  ?start_server:bool -> key:string -> report_progress:(string -> unit) -> 'a -> ('b, string) result

module For_testing : sig
  val call_starting :
    program:string ->
    ?start_server:bool ->
    key:string ->
    report_progress:(string -> unit) ->
    'a ->
    ('b, string) result
end

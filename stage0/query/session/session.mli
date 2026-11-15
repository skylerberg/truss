type t
type attachment = ..
type attachment += Nothing
type start = Own | Near | New

val open_ :
  key:string ->
  ?pointer:string ->
  ?home:string ->
  version:string ->
  bases:(unit -> Engine.t list) ->
  fingerprints:(unit -> (string * string) list) ->
  unit ->
  (t * start, unit) result

val find : string -> t option
val all : unit -> t list
val key : t -> string
val context : t -> Query.context
val observer : t -> Query.context
val engine : t -> Engine.t
val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit
val attachment : t -> attachment
val attach : t -> attachment -> unit
val touch : t -> unit
val fingerprint : string -> string
val note_file : t -> string -> string option -> unit
val trial : t -> t

val snapshot :
  key:string -> pointer:string -> version:string -> bases:(unit -> Engine.t list) -> t option

val homes : unit -> (string * string) list
val save : t -> unit
val stabilize : t -> Engine.change
val compact : ?waited_for:bool -> t -> unit
val sessions : unit -> (string * int) list
val store : unit -> Store.t
val identity : unit -> string
val allow_reading : string -> unit
val directory : string -> string
val cache_directory : string -> string
val results : kind:string -> (string -> string option) * (string -> string -> unit)
val find_result : kind:string -> key:string -> string option
val flush : unit -> unit
val collect : keep:(unit -> (string * string) list) -> unit
val on_close : (unit -> unit) -> unit
val reset : unit -> unit
val recovering : (unit -> 'a) -> 'a
val logging : bool ref

module Graph = Graph

module Server : sig
  val serve :
    key:string ->
    alive:(unit -> bool) ->
    idle:(unit -> unit) ->
    keep:(unit -> (string * string) list) ->
    handle:(progress:(string -> unit) -> 'request -> 'response) ->
    unit

  val call :
    ?program:string ->
    ?start_server:bool ->
    key:string ->
    progress:(string -> unit) ->
    'request ->
    ('response, string) result

  val running : string -> bool
  val serving : unit -> string list
  val stop : unit -> unit
  val store_directory : unit -> string
end

module Identity : sig
  val short : string -> string
end

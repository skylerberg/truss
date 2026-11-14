type attachment = ..
type attachment += Nothing

type t = {
  key : string;
  mutable engine : Engine.t;
  pointer : Store.pointer option;
  version : string;
  bases : Engine.t list;
  mutable used : float;
  fingerprints : (string, string) Hashtbl.t;
  mutable pointed : bool;
  mutable attachment : attachment;
  snapshot_of : string option;
}

type state = { store : Store.t; identity : string; sessions : (string, t) Hashtbl.t }

val logging : bool ref
val on_close : (unit -> unit) -> unit
val store : unit -> Store.t
val identity : unit -> string
val engine : t -> Engine.t
val context : t -> Query.context
val observer : t -> Query.context
val key : t -> string
val attachment : t -> attachment
val attach : t -> attachment -> unit
val touch : t -> unit
val set : t -> ('a, 'b) Query.input -> 'a -> 'b -> unit
val remove : t -> ('a, 'b) Query.input -> 'a -> unit
val find : string -> t option
val allow_reading : string -> unit

type record = { version : string; artifact : string; files : (string * string) list }

val save : t -> unit
val stabilize : t -> Engine.change
val serving : bool ref
val compact : ?waited_for:bool -> t -> unit
val fingerprint : string -> string
val note_file : t -> string -> string option -> unit

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

val trial : t -> t

val snapshot :
  key:string -> pointer:string -> version:string -> bases:(unit -> Engine.t list) -> t option

val homes : unit -> (string * string) list
val sessions : unit -> (string * int) list
val all : unit -> t list
val directory : string -> string
val cache_directory : string -> string
val results : kind:string -> (string -> string option) * (string -> string -> unit)
val find_result : kind:string -> key:string -> string option
val flush : unit -> unit
val reset : unit -> unit
val recovering : (unit -> 'a) -> 'a
val drop_idle : unit -> unit
val collect : keep:(unit -> (string * string) list) -> unit

type snapshot

val take_snapshot : string -> (snapshot * (string * Path.package) list, string) result
val retake : snapshot -> (snapshot, string) result
val root : snapshot -> string
val pipeline : ?checks:bool -> snapshot -> Pipeline.t
val problems : snapshot -> Project.problem list
val packages : snapshot -> (string * Path.package) list
val time_limit_ms : snapshot -> int
val registry_packages : snapshot -> (Path.package * Registry.Version.t * string) list
val lock_fix : snapshot -> string option
val package_files : snapshot -> Path.package -> Path.file list
val dependency_names : snapshot -> Path.package -> Path.package list
val source : snapshot -> Path.file -> Source.t
val file_path : snapshot -> Path.file -> string
val states : unit -> string list
val trial : snapshot -> (string * string option) list -> snapshot
val published : Path.package -> Registry.Version.t -> (snapshot, string) result
val objects_directory : unit -> string
val programs_directory : unit -> string
val results : kind:Store.result_kind -> (string -> string option) * (string -> string -> unit)
val flush : unit -> unit
val store_directory : unit -> string

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

val plan_lock :
  snapshot ->
  set:(Path.package * Registry.Version.t option) list ->
  all:bool ->
  (lock_plan, string) result

val server_key : string -> string
val serve : key:string -> handle:(progress:(string -> unit) -> 'request -> 'response) -> unit

val call :
  ?program:string ->
  ?start_server:bool ->
  ?key:string ->
  progress:(string -> unit) ->
  'request ->
  ('response, string) result

val servers : unit -> string list
val stop : unit -> unit
val reset : unit -> unit

module For_testing : sig
  val standard_state : unit -> Pipeline.state
  val collect_store : unit -> unit
  val interrupt_commit : string -> unit
end

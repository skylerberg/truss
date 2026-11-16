type snapshot

val take_snapshot : string -> (snapshot * (string * Path.package) list, string) result
val retake : snapshot -> (snapshot, string) result
val root : snapshot -> string
val open_database : ?checks:bool -> snapshot -> Database.t
val problems : snapshot -> Project.problem list
val packages : snapshot -> (string * Path.package) list
val time_limit_ms : snapshot -> int
val registry_packages : snapshot -> (Path.package * Registry.Version.t * string) list
val lock_fix : snapshot -> string option
val package_files : snapshot -> Path.package -> Path.file list
val dependency_names : snapshot -> Path.package -> Path.package list
val source : snapshot -> Path.file -> Source.t
val file_path : snapshot -> Path.file -> string
val list_package_databases : unit -> string list
val make_trial : snapshot -> (string * string option) list -> snapshot
val find_base_commit : snapshot -> string option -> string option
val read_commit : snapshot -> string -> (snapshot, string) result

type side = { base : snapshot; other : snapshot; merged : unit -> (snapshot, string) result }

val read_branch : snapshot -> string -> (side, string) result
val read_other_worktree : snapshot -> string -> (side, string) result
val list_other_worktrees : snapshot -> string list
val fetch_published : Path.package -> Registry.Version.t -> (snapshot, string) result
val flush : unit -> unit

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

val plan_lock :
  snapshot ->
  set:(Path.package * Registry.Version.t option) list ->
  all:bool ->
  (lock_plan, string) result

val make_server_key : string -> string
val serve : key:string -> handle:(progress:(string -> unit) -> 'request -> 'response) -> unit

val call :
  ?program:string ->
  ?start_server:bool ->
  ?key:string ->
  progress:(string -> unit) ->
  'request ->
  ('response, string) result

val list_servers : unit -> string list
val stop : unit -> unit
val wait_until_ended : key:string -> unit
val open_cache : unit -> Cache.t
val reset : unit -> unit

module For_testing : sig
  val load_standard_package_database : unit -> Database.package_database
  val build_cold_database : snapshot -> Database.t
  val collect_cache : unit -> unit
  val listen : key:string -> (Unix.file_descr, string) result
  val interrupt_commit : string -> unit
end

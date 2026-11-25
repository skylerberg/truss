type snapshot

val take_snapshot : string -> (snapshot * (string * Path.package) list, string) result
val retake : snapshot -> (snapshot, string) result
val locate_root : snapshot -> string
val open_database : snapshot -> Database.t
val problems : snapshot -> Project.problem list
val list_dependency_problems : snapshot -> Database.t -> Project.problem list
val list_packages : snapshot -> (string * Path.package) list
val time_limit_ms : snapshot -> int
val x86_64_level : snapshot -> X86_64_level.t
val list_registry_packages : snapshot -> (Path.package * Registry.Version.t * string) list
val lock_fix : snapshot -> string option
val list_package_files : snapshot -> Path.package -> Path.file list
val list_dependency_names : snapshot -> Path.package -> Path.package list
val locate_file : snapshot -> Path.file -> string
val list_package_databases : unit -> string list
val make_overlay : snapshot -> (string * string option) list -> snapshot
val flush : unit -> unit

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

val plan_lock :
  snapshot ->
  set:(Path.package * Registry.Version.t option) list ->
  all:bool ->
  (lock_plan, string) result

val find_project_root : string -> string option
val serve : key:string -> handle:(report_progress:(string -> unit) -> 'request -> 'response) -> unit

val call :
  ?start_server:bool ->
  key:string ->
  report_progress:(string -> unit) ->
  'request ->
  ('response, string) result

val list_servers : unit -> string list
val stop_servers : ?key:string -> unit -> bool

exception Unusable_cache of string

val open_cache : unit -> Cache.t
val reset : unit -> unit

module For_testing : sig
  val load_standard_package_database : unit -> string
  val copy_standard_package_database : into:string -> unit
  val build_cold_database : snapshot -> Database.t
  val save : unit -> unit
  val listen : key:string -> (Unix.file_descr, string) result

  val call_starting :
    program:string ->
    ?start_server:bool ->
    key:string ->
    report_progress:(string -> unit) ->
    'request ->
    ('response, string) result

  val remove_ended_servers : unit -> unit
  val interrupt_commit : string -> unit
  val compiler_digest : string
  val observe_logged_bugs : (Compiler_bug.t -> unit) -> unit
end

type session = Session.t

val open_session : string -> (session * (string * Path.package) list, string) result
val refresh : session -> unit
val save_session : session -> unit
val root : session -> string
val context : session -> Query.context
val set : session -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val problems : session -> Project.problem list

val manifest_problems :
  session -> Path.package list -> (string * Path.package * Checks.manifest_problem) list

val packages : session -> (string * Path.package) list
val time_limit_ms : session -> int
val registry_packages : session -> (Path.package * Registry.Version.t * string) list
val lock_fix : session -> string option
val package_modules : session -> Path.package -> Path.module_ list
val package_files : session -> Path.package -> Path.file list
val file_path : session -> Path.file -> string
val diagnostics : session -> Path.file -> Diagnostic.t list
val code_packages : session -> Path.package -> Path.package list
val sessions : unit -> (string * int) list
val trial : session -> (string * string option) list -> session
val base_commit : session -> string option -> string option
val open_commit_of : session -> string -> (session, string) result
val published : Path.package -> Registry.Version.t -> (session, string) result
val objects_directory : unit -> string
val programs_directory : unit -> string
val results : kind:Store.result_kind -> (string -> string option) * (string -> string -> unit)
val flush_store : unit -> unit
val save_opened : unit -> unit
val store_directory : unit -> string
val dependencies : session -> Path.t list -> Graph_types.edge list
val dependents : session -> Path.t list -> Graph_types.edge list
val reachable : session -> Path.t list -> Path.Set.t list
val find_definitions : session -> string -> Path.t list
val changes : session -> session -> (Path.t * Query.part * Graph_types.difference) list
val other_worktrees : session -> session list
val overlap_with : session -> session -> (Graph_types.overlap list, string) result

type merge_diagnostic = { path : string; diagnostic : Diagnostic.t }

val merge_preview : session -> session -> (merge_diagnostic list, string) result

type lock_plan = { text : string; before : Registry.Lock.t; after : Registry.Lock.t }

val plan_lock :
  session ->
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
val recovering : (unit -> 'a) -> 'a
val stop : unit -> unit
val reset : unit -> unit

val load_package :
  Engine.t ->
  name:Path.package ->
  dependencies:Manifest.dependency list ->
  (Path.file * string) list ->
  unit

val load_standard : Engine.t -> unit

module For_testing : sig
  val prepare_store : unit -> unit
  val open_library : ?files:(Path.file * string) list -> string -> (session, string) result
  val set_text : Engine.t -> Path.file -> string -> unit
  val set_manifest : Engine.t -> name:Path.package -> dependencies:Manifest.dependency list -> unit
  val engine : session -> Engine.t
  val session_engine : string -> Engine.t option
  val standard_base : unit -> Engine.t
  val session_base : unit -> Engine.t
  val use_standard : (Path.file * string) list -> unit
  val logging : bool ref
  val collect_store : unit -> unit
end

(** The code database: sessions, which keep each project's packages and modules as inputs and every
    result asked of them current as files change, with each state written to the store as a
    difference over an earlier one; the questions the graph of those results answers; and the
    background process that holds sessions between commands.

    The database answers with data. What a command does with it, and how it is shown, is the command
    line's, in [stage0/cli]; the background process runs the command line's own handler, so a
    command's answer is the same whether a session is in the background process or in the command's
    own. *)

(** {1 Sessions} *)

type session

val open_session : string -> (session * (string * string) list, string) result
(** The session for the project a directory is in, brought up to date with its files, and the
    packages the directory is about: those at or under it, or the one it is in, each as its
    directory relative to the project's root and its name. The project's root is the nearest
    directory at or above whose manifest has a [[project]] table, or with none, the nearest with a
    manifest. An error says why the session cannot be opened, such as no manifest, or another
    process holding it. *)

val refresh : session -> unit
(** Reads the files that changed since the session last looked, after a command changed some. *)

val save_session : session -> unit
(** Saves what the session computed to the store. *)

val root : session -> string
(** The project's root, absolute. *)

val engine : session -> Engine.t
val context : session -> Query.context

val problems : session -> string list
(** What reading the project's manifests shows to be wrong, each as its file and sentences: one that
    could not be read, a package name used twice, a dependency that is no package of the project. *)

val manifest_problems :
  session -> string list -> (string * string * Type_checker.manifest_problem) list
(** What only the code of the named packages shows to be wrong with their manifests: each one's
    file, relative to the project's root, its package, and the problem. Asking checks those
    packages. *)

val packages : session -> (string * string) list
(** Every package of the project: its directory relative to the root, and its name. *)

val time_limit : session -> int
(** The time each test of the project may take, in seconds. *)

val registry_packages : session -> (string * Registry.Version.t * string) list
(** The registry packages of the project's build, in order of name: each one's name, its version,
    and the hash of its files. *)

val lock_fix : session -> string option
(** The lock file the project's manifests give, when the one that is written is another, which is a
    problem whose fix is to write this one. *)

val package_modules : session -> string -> Path.module_ list

val module_file : session -> Path.module_ -> string
(** A module's file, relative to the project's root. *)

val diagnostics : session -> Path.module_ -> Diagnostic.t list
(** A file's diagnostics, kept current and saved. *)

val objects_directory : unit -> string
(** Where object files are cached, in the store. *)

val programs_directory : unit -> string
(** Where programs built to be run are put, in the store. *)

val test_results : unit -> Compile.results
(** Kept test results, in the store. *)

val want : session -> Compile.lowering -> Instance.key list -> unit
(** Adds to the instances whose keys a session has been asked for, which is how code generation is
    given the roots it searches from, as {!Compile.create}'s [want]. *)

val want_in : Engine.t -> Compile.lowering -> Instance.key list -> unit
(** The same, for an engine that is not a session's, as tests have. *)

val flush_store : unit -> unit
(** Writes what the store holds in memory. *)

val sessions : unit -> (string * int) list
(** Each open session, by its worktree or commit, with how many results it holds. *)

(** {1 What reads what} *)

type dependencies

val dependencies : session -> dependencies
(** For every definition of the worktree, what its parts read of other definitions' parts. *)

val reads : dependencies -> Path.t -> (Path.t * string * string) list
(** What a definition reads: each definition, the reader's part, and the part it reads. *)

val readers : dependencies -> Path.t -> (Path.t * string * string) list
(** What reads a definition: each reader, its part, and the part of the definition it reads. *)

val find_definitions : session -> string -> Path.t list
(** The definitions a name means: a full path, or the end of one after [::] or [.]. *)

(** {1 Comparing} *)

type difference = Changed | Added | Same

val base_commit : session -> string option -> string option
(** The commit a revision names, or without one, where the worktree's branch left its default
    branch. *)

val open_commit_of : session -> string -> (session, string) result
(** A session of the worktree's repository at a commit. *)

val changes : session -> session -> (Path.t * string option * difference) list
(** Every part of a definition that a change between the two could reach, in the first, with how it
    compares with the same part in the second. *)

(** {1 Parallel work} *)

type place = { path : Path.t option; part : string option; label : string }
(** A result, by the definition and part it is about, if any, and its label. *)

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }
      (** One worktree's change reads what the other changes *)

val other_worktrees : session -> session list
(** The open sessions of the same project in the other worktrees of its repository. *)

val overlap_with : session -> session -> (overlap list, string) result
(** Where two sessions' changes from their common commit meet. *)

val merge_preview : session -> session -> ((string * string * string) list, string) result
(** The diagnostics a merge of the two would have that neither has: each one's file, code, and
    message. *)

(** {1 The background process} *)

val serve : handle:(progress:(string -> unit) -> 'request -> 'response) -> unit
(** Runs the background process until it has gone three hours without a request, or {!stop} is
    called, answering each request with [handle], which may send text to show while it works with
    [progress]. The client and the process are the same executable, so a request and a response are
    the client's own types. *)

val call :
  ?program:string ->
  ?start_server:bool ->
  progress:(string -> unit) ->
  'request ->
  ('response, string) result
(** Answers a request through the background process for this compiler, starting it from [program],
    this executable unless given, with the argument [__serve], if it is not running, unless
    [start_server] is false, and handing each piece of progress to [progress] as it arrives. *)

val store_directory : unit -> string
(** Where the store is: [$TRUSS_CACHE], or else [$XDG_CACHE_HOME/truss], or else [~/.cache/truss].
*)

val stop : unit -> unit
(** Ends the background process once the request being answered is. *)

(** {1 For tests and drivers} *)

val load_package :
  ?usize_bits:int ->
  Engine.t ->
  name:string ->
  dependencies:Workspace.dependency list ->
  (Path.module_ * string) list ->
  unit
(** Sets a package's modules, with their text, and its manifest as inputs. [usize_bits] is 32 unless
    given. *)

val load_standard : Engine.t -> unit
(** Sets the [standard] package, built into the compiler. *)

val standard_base : unit -> Engine.t
(** The standard library, checked whole and frozen as a fixed base for engines to be made over. *)

type lock_plan = {
  text : string;  (** The lock file as it would be written *)
  before : Registry.Lock.t;
  after : Registry.Lock.t;
}

val plan_lock :
  session -> set:(string * Registry.Version.t option) list -> all:bool -> (lock_plan, string) result
(** The lock file a project would have with other versions: each package of [set] at the version
    given, or at the registry's newest, and with [all], every registry package of the build at its
    newest. The rest follow as a build's versions do. It fetches what it needs and writes no file.
    An error says, in sentences, why there is no such lock file. *)

val published_engine : string -> Registry.Version.t -> (Engine.t, string) result
(** A published package at a version, in an engine of its own with the packages it was published
    with, for comparing a release with it. An error says, as a sentence, why it cannot be had. *)

val code_packages : session -> string -> string list
(** The packages a package's code uses, its tests apart. *)

val trial_with_lock : session -> string -> session
(** A session that starts from another's state, with a lock file in place of its own, for seeing
    what other versions would change before the file is written. *)

val trial : session -> Engine.t
(** An engine that starts from a session's state and changes on its own, for trying a change, such
    as a rename, before any file is written. It shares with the session everything but what the
    trial changes. *)

(** {1 The standard library as a state of its own} *)

type library

val open_library : ?modules:(Path.module_ * string) list -> string -> (library, string) result
(** The standard library as a state of its own, for working on the library: the [standard] package
    is the engine's own inputs, over no base, set from [modules], which are the sources built into
    this compiler unless given. The state is opened from the pointer of that name, so each caller
    that gives its own name keeps its own state, and is kept under {!Compiler_version.digest}, so it
    is found again after an edit to the library, and by a test as by the command line. An error says
    that another process has the state open. *)

val library_engine : library -> Engine.t

val save_library : library -> unit
(** Writes what changed in a library's state to the store, and points its name at it. *)

val reset : unit -> unit
(** Saves and closes every session and the store, so that the next request starts as a new process
    would. *)

val logging : bool ref
(** Whether new sessions keep a log of the queries they compute, for tests. *)

val session_engine : string -> Engine.t option
(** The engine of the open session for a directory, for tests. *)

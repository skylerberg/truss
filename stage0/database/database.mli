(** The code database, as a project sees it: a session for each project's files, kept current as the
    files change, with the project's packages and modules as its inputs; the questions a session's
    graph answers; and the background process that holds sessions between commands.

    This is the project's layer over {!Session}, which keeps states in the store and knows no
    compiler stage. What is here knows manifests, packages, the registry, and git. It names no
    stage's inputs but the project's own: a driver sets a stage's input with {!set}.

    The database answers with data. What a command does with it, and how it is shown, is the command
    line's, in [stage0/cli]; the background process runs the command line's own handler, so a
    command's answer is the same whether a session is in the background process or in the command's
    own. *)

(** {1 Sessions} *)

type session = Session.t
(** One state of a project: a worktree as its files are now, a commit, a change that is only being
    tried, a published package, or the standard library being worked on. Whatever its files come
    from, it is read through {!context}. *)

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
(** The project's root, absolute; empty for a session whose files are in no directory. *)

val context : session -> Query.context
(** What a driver reads a session's results through. *)

val set : session -> ('key, 'value) Query.input -> 'key -> 'value -> unit
(** Sets an input that a stage declares and a driver gives, such as the roots code generation
    searches from, or what the solver said. This is the one way a driver sets an input: the
    project's own inputs, its packages and their modules' text, follow from the session's files. *)

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

val code_packages : session -> string -> string list
(** The packages a package's code uses, its tests apart. *)

val sessions : unit -> (string * int) list
(** Each open session, by what names it, with how many results it holds. *)

(** {1 Other sessions of a project} *)

val trial : session -> (string * string option) list -> session
(** A session that starts from another's state, with some of its files replaced, added, or, with
    [None], removed: each by its path from the project's root. It shares with the session everything
    but what the change reaches and is never saved, so a change, such as a rename or another lock
    file, is checked before any file is written. *)

val base_commit : session -> string option -> string option
(** The commit a revision names, or without one, where the worktree's branch left its default
    branch. *)

val open_commit_of : session -> string -> (session, string) result
(** A session of the worktree's repository at a commit. *)

val published : string -> Registry.Version.t -> (session, string) result
(** A published package at a version, as a session of its own with the packages it was published
    with, for comparing a release with it. An error says, as a sentence, why it cannot be had. *)

val open_library : ?modules:(Path.module_ * string) list -> string -> (session, string) result
(** The standard library as a state of its own, for working on the library: the [standard] package
    is the session's own inputs, over no base, set from [modules], which are the sources built into
    this compiler unless given. The state is opened from the pointer of that name, so each caller
    that gives its own name keeps its own state, and is kept under {!Compiler_version.digest}, so it
    is found again after an edit to the library, and by a test as by the command line. An error says
    that another process has the state open. *)

(** {1 The store} *)

val objects_directory : unit -> string
(** Where object files are cached, in the store. *)

val programs_directory : unit -> string
(** Where programs built to be run are put, in the store. *)

val results : kind:string -> (string -> string option) * (string -> string -> unit)
(** Finding and keeping the results of one kind of expensive step, such as ["tests"], each under the
    key of exactly the input that made it. *)

val flush_store : unit -> unit
(** Writes what the store holds in memory. *)

val prepare_store : unit -> unit
(** Checks the standard library and keeps its state in the store, unless the store has it, as the
    first session opened in a new store does. *)

val store_directory : unit -> string
(** Where the store is: [$TRUSS_CACHE], or else [$XDG_CACHE_HOME/truss], or else [~/.cache/truss].
*)

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

(** {1 Choosing versions} *)

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

val recovering : (unit -> 'a) -> 'a
(** Runs a command that is not answered by the background process. If a state it reads has lost an
    input's value, as after another process collected the store, every open state is discarded and
    the command is run once more, from the files. {!serve} does this for each request. *)

val stop : unit -> unit
(** Ends the background process once the request being answered is. *)

val reset : unit -> unit
(** Saves and closes every session and the store, so that the next request starts as a new process
    would. *)

(** {1 For tests}

    A test holds an engine of its own, which a driver never does. *)

val load_package :
  ?usize_bits:int ->
  Engine.t ->
  name:string ->
  dependencies:Workspace.dependency list ->
  (Path.module_ * string) list ->
  unit
(** Gives an engine a package by itself, as a root of its own: a manifest that says the name, the
    dependencies, and [usize_bits], which is 32 unless given, and a file for each module. *)

val load_standard : Engine.t -> unit
(** Gives an engine the [standard] package, built into the compiler. *)

module Testing : sig
  val set_text : Engine.t -> Path.module_ -> string -> unit
  (** Gives one module of a package set with {!load_package} another text. *)

  val set_manifest :
    ?usize_bits:int -> Engine.t -> name:string -> dependencies:Workspace.dependency list -> unit
  (** Gives a package set with {!load_package} another manifest, and leaves its modules as they are.
  *)

  val engine : session -> Engine.t

  val session_engine : string -> Engine.t option
  (** The engine of the open session for a directory. *)

  val standard_base : unit -> Engine.t
  (** The standard library, checked whole and frozen as a fixed base for engines to be made over. *)

  val logging : bool ref
  (** Whether new sessions keep a log of the queries they compute. *)
end

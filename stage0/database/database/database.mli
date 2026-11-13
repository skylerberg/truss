(** The code database, as a project sees it: a session for each project's files, kept current as the
    files change, with the project's packages and modules as its inputs; the questions a session's
    graph answers; and the background process that holds sessions between commands.

    This is the project's layer over {!Session}, which keeps states in the store and knows no
    compiler stage. This layer knows manifests, packages, the registry, and git. It names no stage's
    inputs but the project's own: a driver sets a stage's input with {!set}.

    The database answers with data. The command's use of it, and how it is shown, is the command
    line's, in [stage0/cli]; the background process runs the command line's own handler, so a
    command's answer is the same whether a session is in the background process or in the command's
    own. *)

(** {1 Sessions} *)

type session = Session.t
(** One state of a project: a worktree as its files are now, a commit, a change that is only being
    tried, a published package, or the standard library being worked on. Whatever its files come
    from, it is read through {!context}. *)

val open_session : string -> (session * (string * Path.package) list, string) result
(** The session for the project a directory is in, brought up to date with its files, and the
    packages the directory is about: those at or under it, or the one it is in, each as its
    directory relative to the project's root and its name. The project's root is the nearest
    directory at or above whose manifest has a [[project]] table, or with none, the nearest with a
    manifest. An error says why the session cannot be opened, such as no manifest, or another
    process holding it. *)

val refresh : session -> unit
(** Reads the files that changed since the session last looked, after a command changed some. *)

val save_session : session -> unit
(** Saves the session's results to the store. *)

val root : session -> string
(** The project's root, absolute; empty for a session whose files are in no directory. *)

val context : session -> Query.context
(** The context a driver reads a session's results through. *)

val set : session -> ('key, 'value) Query.input -> 'key -> 'value -> unit
(** Sets an input that a stage declares and a driver gives, such as the roots of code generation, or
    the solver's answers. This is the one way a driver sets an input: the project's own inputs, its
    packages and their modules' text, follow from the session's files. *)

val problems : session -> string list
(** The errors in the project's manifests, each as its file and sentences: one that could not be
    read, a package name used twice, a dependency that is no package of the project. *)

val manifest_problems :
  session -> Path.package list -> (string * Path.package * Type_checker.manifest_problem) list
(** The errors in the named packages' manifests that only their code shows: each one's file,
    relative to the project's root, its package, and the problem. Asking checks those packages. *)

val packages : session -> (string * Path.package) list
(** Every package of the project: its directory relative to the root, and its name. *)

val time_limit : session -> int
(** The time each test of the project may take, in seconds. *)

val registry_packages : session -> (Path.package * Registry.Version.t * string) list
(** The registry packages of the project's build, in order of name: each one's name, its version,
    and the hash of its files. *)

val lock_fix : session -> string option
(** The lock file the project's manifests give, when the one that is written is another, which is a
    problem whose fix is to write this one. *)

val package_modules : session -> Path.package -> Path.module_ list
val package_files : session -> Path.package -> Path.file list

val file_path : session -> Path.file -> string
(** A file's path, relative to the project's root. *)

val diagnostics : session -> Path.file -> Diagnostic.t list
(** A file's diagnostics, kept current and saved. *)

val code_packages : session -> Path.package -> Path.package list
(** The packages a package's code uses, its tests apart. *)

val sessions : unit -> (string * int) list
(** Each open session, by its name, with how many results it holds. *)

(** {1 Other sessions of a project} *)

val trial : session -> (string * string option) list -> session
(** A session that starts from another's state, with some of its files replaced, added, or, with
    [None], removed: each by its path from the project's root. It shares with the session everything
    but the change's dependents and is never saved, so a change, such as a rename or another lock
    file, is checked before any file is written. *)

val base_commit : session -> string option -> string option
(** The commit a revision names, or without one, where the worktree's branch left its default
    branch. *)

val open_commit_of : session -> string -> (session, string) result
(** A session of the worktree's repository at a commit. *)

val published : Path.package -> Registry.Version.t -> (session, string) result
(** A published package at a version, as a session of its own with the packages it was published
    with, for comparing a release with it. An error says, as a sentence, why it cannot be had. *)

(** {1 The store} *)

val objects_directory : unit -> string
(** Where object files are cached, in the store. *)

val programs_directory : unit -> string
(** Where programs built to be run are put, in the store. *)

val results : kind:string -> (string -> string option) * (string -> string -> unit)
(** Finding and keeping the results of one kind of expensive step, such as ["tests"], each under the
    key of exactly the input that made it. *)

val flush_store : unit -> unit
(** Writes the store's in-memory contents to disk. *)

val store_directory : unit -> string
(** Where the store is: [$TRUSS_CACHE], or else [$XDG_CACHE_HOME/truss], or else [~/.cache/truss].
*)

(** {1 Dependencies}

    An edge records that a part of one definition, such as its body, read a part of another, such as
    its signature, when the session last computed it. The edges over-approximate: a read of a
    lookup, such as a type's impls, is an edge to every definition the lookup read. No read is
    missing. *)

val dependencies : session -> Path.t list -> Graph_types.edge list
(** The edges from the definitions' parts. *)

val dependents : session -> Path.t list -> Graph_types.edge list
(** The edges to the definitions' parts. *)

val reachable : session -> Path.t list -> Path.Set.t list
(** For each root, in order, the definitions it reaches through edges, the root included. *)

val find_definitions : session -> string -> Path.t list
(** The definitions a name means: a full path, or the end of one after [::] or [.]. A method's name
    without its receiver means every version of the method. *)

(** {1 Comparing} *)

val changes : session -> session -> (Path.t * string option * Graph_types.difference) list
(** Every part of a definition that a change between the two could reach, in the first, with how it
    compares with the same part in the second. *)

(** {1 Parallel work} *)

val other_worktrees : session -> session list
(** The sessions of the same project in the other worktrees of its repository: those open in this
    process, and a snapshot of each that a background process serves. *)

val overlap_with : session -> session -> (Graph_types.overlap list, string) result
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
  session ->
  set:(Path.package * Registry.Version.t option) list ->
  all:bool ->
  (lock_plan, string) result
(** The lock file a project would have with other versions: each package of [set] at the version
    given, or at the registry's newest, and with [all], every registry package of the build at its
    newest. The rest follow as a build's versions do. It fetches the packages it needs and writes no
    file. An error says, in sentences, why there is no such lock file. *)

(** {1 The background process} *)

val server_key : string -> string
(** The name of the background process for a directory: the root of the project it is in. *)

val serve : key:string -> handle:(progress:(string -> unit) -> 'request -> 'response) -> unit
(** Runs the background process of a key until it has been idle past its limit, the project's
    directory is gone, or {!stop} is called, answering each request with [handle], which may send
    text to show while it works with [progress]. Each project has a process of its own, so requests
    about different projects, and so different worktrees, are answered at once; those about one
    project are answered one at a time. The client and the process are the same executable, so a
    request and a response are the client's own types. *)

val call :
  ?program:string ->
  ?start_server:bool ->
  ?key:string ->
  progress:(string -> unit) ->
  'request ->
  ('response, string) result
(** Answers a request through the background process of a key, which is that of the current
    directory unless given, starting it from [program], this executable unless given, with the
    arguments [__serve] and the key, if it is not running, unless [start_server] is false, and
    handing each piece of progress to [progress] as it arrives. *)

val servers : unit -> string list
(** The keys of this compiler's background processes that are running. *)

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
  name:Path.package ->
  dependencies:Manifest.dependency list ->
  (Path.file * string) list ->
  unit
(** Gives an engine a package by itself, as a root of its own: a manifest that says the name, the
    dependencies, and [usize_bits], which is 32 unless given, and its files with their texts. *)

val load_standard : Engine.t -> unit
(** Gives an engine the [standard] package, built into the compiler. *)

module For_testing : sig
  val prepare_store : unit -> unit
  (** Checks the standard library and keeps its state in the store, unless the store has it, as the
      first session opened in a new store does. *)

  val open_library : ?files:(Path.file * string) list -> string -> (session, string) result
  (** The standard library as a state of its own, for working on the library: the [standard] package
      is the session's own inputs, over no base, set from [files], which are the sources built into
      this compiler unless given. The state is opened from the pointer of that name, so each caller
      that gives its own name keeps its own state, and is kept under {!Compiler_version.digest}, so
      it is found again after an edit to the library, and by a test as by the command line. An error
      says that another process has the state open. *)

  val set_text : Engine.t -> Path.file -> string -> unit
  (** Gives one file of a package set with {!load_package} another text, adding the file if it has
      none. *)

  val set_manifest :
    ?usize_bits:int ->
    Engine.t ->
    name:Path.package ->
    dependencies:Manifest.dependency list ->
    unit
  (** Gives a package set with {!load_package} another manifest, and leaves its files as they are.
  *)

  val engine : session -> Engine.t

  val session_engine : string -> Engine.t option
  (** The engine of the open session for a directory. *)

  val standard_base : unit -> Engine.t
  (** The standard library, checked whole and frozen as a fixed base for engines to be made over. *)

  val logging : bool ref
  (** Whether new sessions keep a log of the queries they compute. *)
end

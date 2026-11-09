(** The code database: sessions, which keep each worktree's packages and modules as inputs and every
    result asked of them current as files change and saved to the store; the questions the graph of
    those results answers; and the background process that holds sessions between commands. See
    DATABASE.md.

    The database answers with data. What a command does with it, and how it is shown, is the command
    line's, in [stage0/cli]; the background process runs the command line's own handler, so a
    command's answer is the same whether a session is in the background process or in the command's
    own. *)

(** {1 Sessions} *)

type session

val open_session : string -> (session * (string * string) list, string) result
(** The session for the worktree holding a directory, brought up to date with its files, and the
    packages the directory is about: those at or under it, or the one it is in, each as its
    directory relative to the worktree's root and its name. An error says why the session cannot be
    opened, such as another process holding it. *)

val refresh : session -> unit
(** Reads the files that changed since the session last looked, after a command changed some. *)

val save_session : session -> unit
(** Saves what the session computed to the store. *)

val root : session -> string
(** The worktree's root, absolute. *)

val engine : session -> Engine.t
val context : session -> Query.context

val problems : session -> string list
(** Manifests that could not be read, and package names used twice, each as a sentence. *)

val packages : session -> (string * string) list
(** Every package of the worktree: its directory relative to the root, and its name. *)

val package_modules : session -> string -> Path.module_ list

val module_file : session -> Path.module_ -> string
(** A module's file, relative to the worktree's root. *)

val diagnostics : session -> Path.module_ -> Diagnostic.t list
(** A file's diagnostics, kept current and saved. *)

val objects_directory : unit -> string
(** Where object files are cached, in the store. *)

val programs_directory : unit -> string
(** Where programs built to be run are put, in the store. *)

val test_results : unit -> Compile.results
(** Kept test results, in the store. *)

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
(** The open sessions of the other worktrees of the same repository. *)

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

val standard_layer : ?log:bool -> unit -> Engine.t
(** A frozen layer with the standard library set. *)

val reset : unit -> unit
(** Saves and closes every session and the store, so that the next request starts as a new process
    would. *)

val logging : bool ref
(** Whether new sessions keep a log of the queries they compute, for tests. *)

val session_engine : string -> Engine.t option
(** The engine of the open session for a directory, for tests. *)

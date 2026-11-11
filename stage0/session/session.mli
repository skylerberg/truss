(** The code database's sessions: states with their place in the store, the questions a state's
    graph answers, and the background process that holds sessions between commands.

    This layer knows no compiler stage and no project: not what a manifest is, nor a package, nor
    git. A client, such as {!Database}, says what a session's inputs are and keeps what it needs
    with each session as its {!attachment}. So the layer can be given another client, and a client
    another layer, without either changing. *)

type t
(** One state, with the name it is saved under in the store, if it is saved. *)

type attachment = ..
(** What a client keeps with a session. This layer does not look inside. *)

type attachment += Nothing

type start =
  | Own  (** The state the session's own name pointed at, or a session that was already open *)
  | Near  (** The saved state nearest to the session's files, which another name points at *)
  | New  (** A new state over the bases *)

val open_ :
  key:string ->
  ?pointer:string ->
  ?home:string ->
  version:string ->
  bases:(unit -> Engine.t list) ->
  fingerprints:(unit -> (string * string) list) ->
  unit ->
  (t * start, unit) result
(** The session of a key, opened if it is not open. With [pointer], its state is saved under that
    name, and opened from it; an error says that another process holds the name. A session with no
    state of its own starts from the saved state of the same [version] whose files' fingerprints are
    nearest to [fingerprints], each a file's path and {!fingerprint}, or, with none, as a new state
    over [bases]. [version] names the code that computes the state's results, and is part of every
    key. [home] is a directory whose removal makes the saved state garbage. *)

val find : string -> t option
(** The open session of a key. *)

val all : unit -> t list
val key : t -> string

val context : t -> Query.context
(** For a driver's reads. Each result read through it becomes a root of the state. *)

val observer : t -> Query.context
(** For a driver's reads that make no root. *)

val engine : t -> Engine.t
(** For the client that says what the session's inputs are, and for tests. *)

val set : t -> ('key, 'value) Query.input -> 'key -> 'value -> unit
val remove : t -> ('key, 'value) Query.input -> 'key -> unit
val attachment : t -> attachment
val attach : t -> attachment -> unit

val touch : t -> unit
(** Says the session was used now. One not used for an hour is saved and closed. *)

val fingerprint : string -> string
(** A file's fingerprint, from its text. *)

val note_file : t -> string -> string option -> unit
(** Records a file's fingerprint, or with [None] that the file is gone, for other sessions to find
    this state by. *)

val trial : t -> t
(** A session that starts from another's state and changes on its own. The two share everything but
    what the trial changes. It is never saved, and has no attachment. *)

val save : t -> unit
(** Writes what changed in the state since it was last written, and points its name at it. *)

val stabilize : t -> Engine.change
(** Brings the state up to date, and saves it. *)

val fold : ?waited_for:bool -> t -> unit
(** Writes the state whole and opens it again, once what was written since the last whole state has
    grown to half its size; with [waited_for], in the background process, only at four times that,
    since a command is waiting. *)

val sessions : unit -> (string * int) list
(** Each open session's key, with how many results it holds. *)

(** {1 The store} *)

val store : unit -> Store.t

val identity : unit -> string
(** The compiler's identity: the hash of its executable, which is the version of a state whose
    client names no other. *)

val trust : string -> unit
(** Names a version, other than the compiler's identity, whose states this program can read, so that
    collection keeps what they hold. *)

val directory : string -> string
(** A directory of the store, for results that must be files. *)

val results : kind:string -> (string -> string option) * (string -> string -> unit)
(** Finding and keeping the results of one kind, each under a key. *)

val find_result : kind:string -> key:string -> string option
val add_result : kind:string -> key:string -> string -> unit
val flush : unit -> unit

val on_close : (unit -> unit) -> unit
(** Runs a function whenever every state is closed or discarded, for a client to let go of what it
    built on them. *)

val reset : unit -> unit
(** Saves and closes every session and the store, so that the next request starts as a new process
    would. *)

val recovering : (unit -> 'a) -> 'a
(** Runs a command. If a state it reads has lost an input's value, every open state is discarded
    with its pointer, and the command is run once more. *)

val logging : bool ref
(** Whether new sessions keep a log of the queries they compute, for tests. *)

(** {1 What a state's graph answers} *)

module Graph : sig
  type dependencies

  val dependencies : Engine.t -> dependencies
  (** For every definition a state holds results about, what its parts read of other definitions'
      parts. *)

  val reads : dependencies -> Path.t -> (Path.t * string * string) list
  val readers : dependencies -> Path.t -> (Path.t * string * string) list

  type difference = Changed | Added | Same

  val changes : Engine.t -> Engine.t -> (Path.t * string option * difference) list
  (** Every part of a definition that a change between two states could reach, in the first, with
      how it compares with the same part in the second. *)

  type place = { path : Path.t option; part : string option; label : string }

  type overlap =
    | Both_change of place
    | Reads of { this_worktree : bool; change : place; reads : place }

  val overlaps : base:Engine.t -> Engine.t -> Engine.t -> overlap list
  (** Where two states' changes from a common base meet. *)
end

(** {1 The background process} *)

module Server : sig
  val serve :
    idle:(unit -> unit) ->
    keep:(unit -> (string * string) list) ->
    handle:(progress:(string -> unit) -> 'request -> 'response) ->
    unit
  (** Runs the background process until it has gone three hours without a request, or {!stop} is
      called. [idle] runs each second that no request waits, and [keep] names states to keep when
      the store is collected, each as its version and artifact. *)

  val call :
    ?program:string ->
    ?start_server:bool ->
    progress:(string -> unit) ->
    'request ->
    ('response, string) result

  val stop : unit -> unit
  val store_directory : unit -> string
end

module Identity : sig
  val short : string -> string
end

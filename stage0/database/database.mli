(** The code database's sessions and requests: what the command line, the language server, and agent
    tools see. See DATABASE.md, "Sessions" and "Requests".

    A session holds one worktree's state: its packages and modules as inputs, and every result its
    requests asked for, kept current as files change and saved to the store. Requests and answers
    are the same whether a session runs in the background process or in the client's own process. *)

type command =
  | Check  (** Every diagnostic and hole *)
  | Test of { sanitize : bool }  (** Each test's outcome *)
  | Build of { output : string; sanitize : bool }  (** The package's program *)
  | Run of { sanitize : bool }  (** The program built, for the client to run *)
  | Impact of { base : string option }  (** What the worktree's changes from a commit affect *)
  | Holes  (** Each [todo], and what it blocks *)
  | References of { name : string }  (** What reads a definition *)
  | Dependencies of { name : string }  (** What a definition reads *)
  | Overlap of { other : string option; merge : bool }
      (** Where this worktree's changes meet another's, or a branch's *)
  | Explain of { file : string; line : int; column : int }
      (** What is at a position: a name's meaning, and the signature it refers to *)
  | Sync  (** Nothing, once every change made before the request has been seen *)
  | Status  (** The background process's sessions *)
  | Stop  (** Ends the background process *)

type request = { directory : string; command : command; json : bool }

type response = {
  output : string;
  errors : string;
  status : int;  (** 0 for success, 1 for errors in the code, 2 when the request could not run *)
  program : string option;  (** For [Run]: the program built, which the client runs and removes *)
}

val handle : request -> response
(** Answers a request in this process. *)

val call : ?program:string -> request -> response
(** Answers a request through the background process for this compiler, starting it from [program],
    this executable unless given, with the argument [__serve], if it is not running. *)

val serve : unit -> unit
(** Runs the background process until it has gone three hours without a request, or is asked to
    stop. *)

(** {1 For tests and drivers} *)

val load_package :
  Engine.t ->
  name:string ->
  dependencies:Workspace.dependency list ->
  (Path.module_ * string) list ->
  unit
(** Sets a package's modules, with their text, and its manifest as inputs. *)

val load_standard : Engine.t -> unit
(** Sets the [standard] package, built into the compiler. *)

val standard_layer : ?log:bool -> unit -> Engine.t
(** A frozen layer with the standard library set. *)

val read_directory : package:string -> string -> (Path.module_ * string) list
(** The modules of a package's directory: each [.truss] file under it, named by its path there, in
    order. *)

val reset : unit -> unit
(** Saves and closes every session and the store, so that the next request starts as a new process
    would. *)

val session_engine : string -> Engine.t option
(** The engine of the open session for a directory, for tests. *)

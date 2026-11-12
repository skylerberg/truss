(** The code database's store on disk: values by the hash of their bytes, results by the hash of the
    input that made them, and pointers to the states being worked on.

    Values and results live in append-only segment files. Each process that writes has a segment of
    its own, so writers never share a file or take a lock to write. A full segment is sealed with a
    sorted index beside it, which is read into memory as one string and searched by halving. Every
    record carries a checksum, so a record cut short by a crash, or damaged later, is treated as
    missing. Only ordinary file operations are used: create, append, read, rename, flush to disk,
    and delete. *)

type t

val open_ : string -> t
(** The store in a directory, which is made if it does not exist. *)

val close : t -> unit
(** Seals this process's segment. *)

val default_directory : unit -> string
(** [$TRUSS_CACHE], else [$XDG_CACHE_HOME/truss], else [~/.cache/truss]. *)

val directory : t -> string

(** {1 Values} *)

val put : t -> string -> string
(** Adds bytes, and returns their name: the 32-byte BLAKE3 hash. Adding bytes the store has already
    adds nothing. *)

val get : t -> string -> string option
(** The bytes with that name, or [None] if the store does not have them. A miss looks for what other
    processes added since the store last looked, at most every twenty milliseconds. *)

val refresh : t -> unit
(** Looks now for what other processes added, before reading what one of them just wrote. *)

val flush : t -> unit
(** Makes every value and result added so far durable, before a pointer refers to them. *)

(** {1 Results} *)

val find_result : t -> kind:string -> key:string -> string option
(** The result of a kind, such as ["tests"], kept under a key: exactly the input that made it, or
    its hash. *)

val add_result : t -> kind:string -> key:string -> string -> unit

val files : t -> string -> string
(** A directory of the store for results that must be files, such as object files, which a linker
    reads by path. *)

(** {1 Pointers} *)

type pointer
(** A named place that holds a few bytes and is replaced whole, such as the name of a worktree's
    current state. Everything else in the store is named by what it holds and never changes. *)

val pointer : t -> string -> pointer

val lock : pointer -> bool
(** Takes the pointer for this process alone, while it lives; [false] if another process has it. *)

val unlock : pointer -> unit
(** Gives up a pointer taken with {!lock}. *)

val read : pointer -> string option
(** What the pointer holds, or [None] if it was never written, or is cut short or damaged. *)

val point : pointer -> string -> unit
(** Replaces what the pointer holds, after making every value and result added so far durable. *)

val remove_pointer : pointer -> unit
val pointers : t -> string list

(** {1 Collection} *)

val compact : t -> unit
(** Gathers small segments that no running process is writing into this process's segment, once
    there are many, so that a lookup searches fewer. Every record is kept. *)

val size : t -> int
(** The bytes the store's segments take. *)

val collect : t -> budget:int -> live:(string -> bool) -> unit
(** When the segments take more than [budget] bytes, copies into a new segment every value [live]
    names, and every result read or added by this process or added in the last week, and deletes the
    segments copied from. Segments that another running process is still writing are left alone. *)

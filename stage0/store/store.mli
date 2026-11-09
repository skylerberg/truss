(** The code database's store on disk: values by the hash of their bytes, results by the hash of the
    input that made them, and append-only journals. See DATABASE.md, "Content hashes and the store".

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
(** The bytes with that name, or [None] if the store does not have them. *)

val flush : t -> unit
(** Makes every value and result added so far durable, before a journal refers to them. *)

(** {1 Results} *)

val find_result : t -> kind:string -> key:string -> string option
(** The result of a kind, such as ["tests"], kept under a key: the hash of exactly the input that
    made it. *)

val add_result : t -> kind:string -> key:string -> string -> unit

val files : t -> string -> string
(** A directory of the store for results that must be files, such as object files, which a linker
    reads by path. *)

(** {1 Journals} *)

type journal

val journal : t -> string -> journal
(** A session's journal, by name. *)

val lock : journal -> bool
(** Takes the journal for this process alone, while it lives; [false] if another process has it. *)

val unlock : journal -> unit
(** Gives up a journal taken with {!lock}. *)

val records : journal -> string list
(** Every whole record, in the order appended. Reading stops at the first record that is cut short
    or damaged. *)

val append : journal -> string -> unit
(** Appends a record and makes it durable, after flushing the store's values. *)

val compact : journal -> string -> unit
(** Replaces every record with one, written beside the journal and renamed over it. *)

val journal_name : journal -> string
(** The journal's file, which names it. *)

val journal_size : journal -> int
val remove_journal : journal -> unit
val journals : t -> string list

(** {1 Collection} *)

val size : t -> int
(** The bytes the store's segments take. *)

val collect : t -> budget:int -> live:(string -> bool) -> unit
(** When the segments take more than [budget] bytes, copies into a new segment every value [live]
    names, and every result read or added by this process or added in the last week, and deletes the
    segments copied from. Segments that another running process is still writing are left alone. *)

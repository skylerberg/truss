(** A package's files, and the hash that names them. *)

val skipped : string -> bool
(** Whether a directory's name is one that never holds a package's files: one that starts with [.],
    [_build], and [node_modules]. *)

val hash : (string * string) list -> string
(** The hash of a package's files, each a path and its bytes, as SYNTAX.md's "The lock file" defines
    it: the BLAKE3 hash of a line for each file, in order of path, with the path, a space, and the
    BLAKE3 hash of the file's bytes. It is 64 hexadecimal digits. *)

val is_hash : string -> bool

val files : ?all:bool -> string -> (string * string) list
(** The files of the package in a directory that are published, each by its path from the directory,
    with its bytes, in order of path: its manifest, its lock file, its modules, and the Markdown
    files beside them, leaving out the directories of other packages. With [all], every file under
    the directory, which is what a published package's directory holds. *)

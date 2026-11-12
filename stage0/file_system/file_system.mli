(** Whole-file reads and writes, and directories. *)

val read : string -> string
val write : string -> string -> unit

val write_all : Unix.file_descr -> string -> unit
(** Writes all of a string to a descriptor, however many writes it takes. *)

val write_atomically : ?durable:bool -> string -> string -> unit
(** [write_atomically path text] writes [text] to a temporary file beside [path] and renames it over
    [path], so a reader sees the old contents or the new, never part of them. The temporary name
    holds the process id, so two processes writing one path do not write the same temporary file.
    With [~durable:true] the contents reach the disk before the rename, so a crash cannot leave
    [path] naming lost data. *)

val make_directory : string -> unit
(** Makes a directory and every missing directory above it. A directory that exists, including one
    another process makes at the same time, is not an error. *)

val remove : string -> unit
(** Removes a file, or a directory and everything in it. A path that does not exist is not an error.
*)

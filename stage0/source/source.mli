(** A source file: its path, its bytes, and the start of each line.

    Every position in the compiler is a byte offset into a file's original
    bytes. Lines and columns are worked out only when a position is shown. *)

type span = { start : int; stop : int }
(** Byte offsets: [start] is included and [stop] is not. *)

type t

val create : path:string -> string -> t
val read_file : string -> t
val path : t -> string
val text : t -> string

val position : t -> int -> int * int
(** [position source offset] is the line and column of [offset], both
    counting from 1. Columns count Unicode scalar values, as editors do, and
    a byte order mark at the start of the file is not counted. A line break
    is a line feed, a carriage return followed by a line feed, or a carriage
    return on its own, which the scanner reports but still treats as a line
    break. *)

val line_start : t -> int -> int
(** The offset where the line holding [offset] starts. *)

val line_end : t -> int -> int
(** The offset of the line break that ends the line holding [offset], or the
    end of the file. *)

val starts_line : t -> int -> bool
(** Whether nothing comes before [offset] on its line, not even whitespace. A
    byte order mark at the start of the file does not count. *)

val byte_order_mark_length : t -> int
(** 3 if the file starts with a byte order mark, and 0 otherwise. *)

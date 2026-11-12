(** A source file: its path, its bytes, and the start of each line.

    Every position in the compiler is a byte offset into a file's original bytes. Lines and columns
    are computed only when a position is shown. A byte order mark at the start of the file comes
    before the first line, so no line or column counts it. *)

type span = private { start : int; stop : int }
(** Byte offsets into the file: [start] is included and [stop] is not. Spans are made only with
    {!span}, so [0 <= start <= stop] always holds. *)

val span : int -> int -> span
(** [span start stop]. Raises [Invalid_argument] unless [0 <= start <= stop]. *)

val zero_width : int -> span

type t

val create : path:string -> string -> t
val read_file : string -> t
val path : t -> string
val text : t -> string

val position : t -> int -> int * int
(** [position source offset] is the line and column of [offset], both counting from 1. Columns count
    Unicode scalar values, as terminals and most editors do; the Language Server Protocol counts
    UTF-16 code units by default. A line break is a line feed, a carriage return followed by a line
    feed, or a carriage return on its own, which the scanner reports but still treats as a line
    break. *)

val line_start : t -> int -> int
(** The offset where the line holding [offset] starts. The first line starts after a byte order
    mark. *)

val line_end : t -> int -> int
(** The offset of the line break that ends the line holding [offset], or the end of the file. *)

val starts_line : t -> int -> bool
(** Whether nothing comes before [offset] on its line, not even whitespace. *)

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
    Unicode scalar values, as terminals and most editors do; {!location} counts other units. A line
    break is a line feed, a carriage return followed by a line feed, or a carriage return on its
    own, which the scanner reports but still treats as a line break. *)

(** What a column counts. *)
type units = Bytes | Scalar_values | Utf_16_code_units

val location : units -> t -> int -> int * int
(** [location units source offset] is the line and column of [offset], both counting from 0, the
    column in [units]. Lines break as in {!position}. *)

val offset : units -> t -> line:int -> column:int -> int
(** The inverse of {!location}: the byte offset of a line and column counting from 0. A column past
    the end of its line gives the end of the line, and a line past the end of the file gives the end
    of the file. *)

val line_start : t -> int -> int
(** The offset where the line holding [offset] starts. The first line starts after a byte order
    mark. *)

val fragment_line_start : string -> int -> int
(** [fragment_line_start text offset] is the offset where the line holding [offset] starts in
    [text], a part of a file such as one definition's text. Lines break as in {!position}. *)

val line_end : t -> int -> int
(** The offset of the line break that ends the line holding [offset], or the end of the file. *)

val starts_line : t -> int -> bool
(** Whether nothing comes before [offset] on its line, not even whitespace. *)

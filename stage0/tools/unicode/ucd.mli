(** Reading the files of the Unicode character database. Each function that reads a file takes the
    database's directory and the file's name. *)

val read_lines : string -> string -> string list

val records : string -> string -> string list list
(** The fields of each data line of a semicolon-separated file, trimmed, with comments and blank
    lines left out. *)

val code_point : string -> int
(** A code point written in hexadecimal. *)

val code_point_range : string -> int * int
(** [first..last], or one code point. *)

val merge : (int * int) list -> (int * int) list
(** The ranges sorted, with the ones that touch or overlap joined. *)

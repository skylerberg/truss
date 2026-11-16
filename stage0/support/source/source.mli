type span = private { start : int; stop : int }

val make_span : int -> int -> span
val make_zero_width : int -> span

module Definition_span : sig
  type t = private { start : int; stop : int }

  val make : int -> int -> t
  val make_zero_width : int -> t
  val to_file : base:int -> t -> span
  val of_file : base:int -> span -> t
  val locate : t array -> int -> t
  val quote : string -> t -> string
end

type t

val create : path:string -> string -> t
val read_file : string -> t
val path : t -> string
val text : t -> string
val compute_position : t -> int -> int * int

type units = Bytes | Scalar_values | Utf_16_code_units

val compute_location : units -> t -> int -> int * int
val compute_offset : units -> t -> line:int -> column:int -> int
val compute_line_start : t -> int -> int
val compute_fragment_line_start : string -> int -> int
val compute_line_end : t -> int -> int
val starts_line : t -> int -> bool

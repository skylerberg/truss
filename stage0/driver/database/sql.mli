type t
type row
type argument = Blob of string | Text of string | Integer of int | Null

exception Failed of string

val open_memory : unit -> t
val open_file : string -> t
val open_immutable_file : string -> t
val close : t -> unit
val attach_immutable_file : t -> schema:string -> string -> unit
val detach : t -> schema:string -> unit
val run_script : t -> string -> unit
val run : t -> string -> argument list -> unit
val find_row : t -> string -> argument list -> (row -> 'value) -> 'value option
val list_rows : t -> string -> argument list -> (row -> 'value) -> 'value list
val has_row : t -> string -> argument list -> bool
val count_changes : t -> int
val read_blob : row -> int -> string
val read_text : row -> int -> string
val read_integer : row -> int -> int
val is_null : row -> int -> bool
val read_cell : row -> int -> argument
val with_observer : (string -> unit) -> (unit -> 'result) -> 'result
val begin_transaction : t -> unit
val commit_transaction : t -> unit
val roll_back_transaction : t -> unit
val checkpoint : t -> unit
val run_outside_transaction : t -> (unit -> unit) -> unit
val copy_into : source:t -> schema:string -> t -> unit

type t

val open_ : string -> t
val close : t -> unit
val default_directory : unit -> string
val directory : t -> string
val put : t -> string -> string
val get : t -> string -> string option
val refresh : t -> unit
val flush : t -> unit

type result_kind = Package_state | Test_result | Solver_answer | Fact | Reads

val find_result : t -> kind:result_kind -> key:string -> string option
val add_result : t -> kind:result_kind -> key:string -> string -> unit
val files : t -> string -> string
val cache_files : t -> string -> string

type pointer

val pointer : t -> string -> pointer
val lock : pointer -> bool
val unlock : pointer -> unit
val read : pointer -> string option
val write_pointer : pointer -> string -> unit
val remove_pointer : pointer -> unit
val pointers : t -> string list
val compact : t -> unit
val size : t -> int
val collect : t -> budget:int -> live:(string -> bool) -> unit

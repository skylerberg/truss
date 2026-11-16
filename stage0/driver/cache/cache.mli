type t

val open_ : string -> t
val close : t -> unit
val default_directory : unit -> string
val directory : t -> string
val flush : t -> unit

type result_kind = Package_database | Test_result | Solver_answer

val find_result : t -> kind:result_kind -> key:string -> string option
val add_result : t -> kind:result_kind -> key:string -> string -> unit
val make_objects_directory : t -> string
val make_packages_directory : t -> string
val make_programs_directory : t -> string
val compact : t -> unit
val collect : t -> budget:int -> unit

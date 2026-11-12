exception Stop of int

val mains : Project.t -> Path.t list
val run : directory:string -> release:bool -> sanitize:bool -> arguments:string list -> Outcome.t
val build : directory:string -> output:string option -> json:bool -> Outcome.t

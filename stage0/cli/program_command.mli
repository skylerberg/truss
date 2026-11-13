val mains : Project.t -> Path.t list
val run : release:bool -> arguments:string list -> Outcome.t
val build : output:string option -> Outcome.t

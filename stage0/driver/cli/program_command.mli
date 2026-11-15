val mains : Database.snapshot -> Path.package list -> Path.t list
val run : release:bool -> arguments:string list -> Outcome.t
val build : output:string option -> Outcome.t

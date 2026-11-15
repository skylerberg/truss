type t = { stage : string; message : string; doing : string list }

exception Bug of t

val bug : stage:string -> ('a, unit, string, 'b) format4 -> 'a
val while_doing : stage:string -> string -> (unit -> 'a) -> 'a
val to_string : t -> string

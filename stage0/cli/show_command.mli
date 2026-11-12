module Names = Resolve.Names

type found = { declaration : Names.declaration; file : string; line : int; text : string }

val find : Project.t -> body:bool -> string -> found list
val run : directory:string -> paths:string list -> body:bool -> json:bool -> int

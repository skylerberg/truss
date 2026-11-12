module Names = Resolve.Names

val offset_of : String.t -> line:int -> column:int -> int
val run : directory:string -> position:string -> json:bool -> int

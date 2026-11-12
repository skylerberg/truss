val chosen : Diagnostic.t list -> Diagnostic.t list
val apply : string -> Diagnostic.edit list -> string
val run : directory:string -> fix:bool -> json:bool -> int

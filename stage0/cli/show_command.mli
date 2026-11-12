module Names = Resolve.Names

type shown_definition = {
  declaration : Names.declaration;
  file : string;
  line : int;
  text : string;
}

val find : Project.t -> body:bool -> string -> shown_definition list
val run : directory:string -> paths:string list -> body:bool -> json:bool -> int

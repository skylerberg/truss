module Names = Resolve.Names

type hole = {
  definition : Path.t;
  file : string;
  line : int;
  column : int;
  type_ : string option;
  in_scope : (string * string) list;
  mutable blocks : string list;
}

val gather : Project.t -> string list -> hole list
val fill_blocks : Project.t -> hole list -> unit
val run : directory:string -> paths:string list -> json:bool -> int

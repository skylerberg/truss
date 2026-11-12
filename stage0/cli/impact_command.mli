module Names = Resolve.Names

type change = {
  path : Path.t;
  status : [ `Added | `Changed of string list | `Removed ];
  before : string option;
  after : string option;
  read_by : (Path.t * string * string) list;
}

val changes : Project.t -> Database.session -> change list
val run : directory:string -> base:string option -> json:bool -> int

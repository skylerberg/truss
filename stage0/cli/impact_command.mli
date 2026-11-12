module Names = Resolve.Names

type change = {
  path : Path.t;
  status : [ `Added | `Changed of string list | `Removed ];
  before : string option;
  after : string option;
  dependents : Database.edge list;
}

val changes : Project.t -> Database.session -> change list
val run : directory:string -> base:string option -> json:bool -> int

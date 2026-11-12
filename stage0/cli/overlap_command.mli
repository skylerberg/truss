val sentence : Database.overlap -> string

type found = {
  other : string;
  overlaps : Database.overlap list;
  merged : (string * string * string) list;
  error : string option;
}

val to_json : found list -> Json.t
val print : found list -> unit
val with_other_worktrees : Database.session -> found list
val run : directory:string -> with_:string option -> merge:bool -> json:bool -> int

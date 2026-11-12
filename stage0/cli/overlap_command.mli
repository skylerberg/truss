type comparison = {
  other : string;
  overlaps : Graph_types.overlap list;
  merged : (string * string * string) list;
  error : string option;
}

val to_json : comparison list -> Json.t
val print : comparison list -> unit
val with_other_worktrees : Database.session -> comparison list
val run : directory:string -> with_:string option -> merge:bool -> json:bool -> int

module For_testing : sig
  val sentence : Graph_types.overlap -> string
end

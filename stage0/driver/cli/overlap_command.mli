type comparison

val to_json : comparison list -> Json.t
val print : comparison list -> unit
val with_other_worktrees : Workspace.snapshot -> Database.t -> comparison list
val run : with_:string option -> merge:bool -> int

type dependencies = (Path.t, (Path.t * string * string) list) Hashtbl.t

val dependencies : Engine.t -> dependencies
val reads : dependencies -> Path.t -> (Path.t * string * string) list
val readers : dependencies -> Path.t -> (Path.t * string * string) list

type difference = Changed | Added | Same

val changes : Engine.t -> Engine.t -> (Path.t * string option * difference) list

type place = { path : Path.t option; part : string option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

val overlaps : base:Engine.t -> Engine.t -> Engine.t -> overlap list

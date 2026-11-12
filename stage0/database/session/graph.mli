type edge = {
  dependent : Path.t;
  dependent_part : string;
  dependency : Path.t;
  dependency_part : string;
}

val dependencies : Engine.t -> Path.t list -> edge list
val dependents : Engine.t -> Path.t list -> edge list
val reachable : Engine.t -> Path.t list -> Path.Set.t list

type difference = Changed | Added | Same

val changes : Engine.t -> Engine.t -> (Path.t * string option * difference) list

type place = { path : Path.t option; part : string option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

val overlaps : base:Engine.t -> Engine.t -> Engine.t -> overlap list

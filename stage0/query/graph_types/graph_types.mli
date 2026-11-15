type edge = {
  dependent : Path.t;
  dependent_part : string;
  dependency : Path.t;
  dependency_part : string;
}

type difference = Changed | Added | Same
type place = { path : Path.t option; part : string option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

type edge = {
  dependent : Path.t;
  dependent_part : Query.part;
  dependency : Path.t;
  dependency_part : Query.part;
}

type difference = Changed | Added | Same
type place = { subject : Query.subject option; label : string }

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }

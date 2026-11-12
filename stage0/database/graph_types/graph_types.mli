(** The answers of graph questions about a state. Each names definitions and parts, never the
    engine's nodes. *)

type edge = {
  dependent : Path.t;
  dependent_part : string;
  dependency : Path.t;
  dependency_part : string;
}
(** A part of one definition, the dependent, read a part of another when the state last computed it.
*)

type difference = Changed | Added | Same

type place = { path : Path.t option; part : string option; label : string }
(** A result, by the definition and part it is about, if any, and its label. *)

type overlap =
  | Both_change of place
  | Reads of { this_worktree : bool; change : place; reads : place }
      (** One worktree's change depends on a change of the other *)

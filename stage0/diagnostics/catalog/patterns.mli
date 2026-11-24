type t =
  | Shadowing_arm of {
      arm : Core.origin;
      name : string;
      constant : Path.t;
      bindings : Core.origin list;
    }
  | Unreachable_arm of { arm : Core.origin }
  | Unreachable_alternative of {
      alternative : Core.origin;
      previous : Core.origin option;
      next : Core.origin option;
      is_after_alternatives : bool;
    }
  | Not_covered of {
      match_ : Core.origin;
      last_arm : Core.origin option;
      witness : string;
      other_witnesses : string list;
      may_have_more : bool;
    }
  | Refutable of { pattern : Core.origin; witness : string }

val describe : t -> Nodes.description
val list_examples : Diagnostic.Code.patterns -> t list

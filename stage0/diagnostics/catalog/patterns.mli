type witness =
  | Any
  | Boolean of bool
  | Integers of { low : Z.t; high : Z.t }
  | Variant of { variant : string; fields : field_witness list }
  | Record of field_witness list

and field_witness = { field : string; witness : witness }

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
      witness : witness list;
      other_witnesses : witness list list;
      may_have_more : bool;
    }
  | Refutable of { pattern : Core.origin; witness : witness }

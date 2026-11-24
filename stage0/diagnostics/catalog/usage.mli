type removal =
  | Wildcard
  | Field_wildcard
  | Field_deletion of { field : Core.origin; next : Core.origin }

type occurrence = { binding : Core.origin; removal : removal }

type t =
  | Unread_variable of { binding : Core.origin; name : string }
  | Unused_variable of {
      name : string;
      binding : occurrence;
      alternatives : occurrence list;
      constant : Path.t option;
    }
  | Unreachable_code of { first : Core.origin; last : Core.origin }
  | Self_comparison of {
      comparison : Core.origin;
      operand : Core.origin;
      operator : Language.Comparison.t;
      is_float : bool;
    }
  | Unused_run_forever of {
      function_ : Path.t;
      entry : Core.origin Description.range;
      siblings : Core.origin Description.siblings;
    }
  | Unmodified_part of {
      entry : Core.origin;
      function_ : Path.t;
      parameter : string;
      fields : string list;
      change : part_change;
    }
  | Unused_definition of {
      name : Core.origin;
      definition : Path.t;
      kind : definition_kind;
      visibility : visibility;
      is_used_by_unused : bool;
    }

and part_change =
  | Named_part_changed of Core.origin Description.siblings
  | Unnamed_part_changed
  | Parameter_unchanged

and definition_kind = Function | Constant
and visibility = Internal | Private

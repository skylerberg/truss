type root = Local of Core.local | Temporary of Mir.local | Constant of Path.t | Environment
type step = Field of string | Element of { node : Core.id; origin : Core.origin }
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.origin * Core.origin

let classify_overlap left right =
  if left.root <> right.root then Disjoint
  else
    let rec classify_steps left right =
      match (left, right) with
      | [], _ | _, [] -> Overlapping
      | Field first :: left, Field second :: right ->
          if first = second then classify_steps left right else Disjoint
      | Element first :: left, Element second :: right -> (
          if first.node = second.node then classify_steps left right
          else
            match classify_steps left right with
            | Disjoint -> Disjoint
            | _ -> Maybe_disjoint (first.origin, second.origin))
      | _ :: left, _ :: right -> classify_steps left right
    in
    classify_steps left.steps right.steps

let is_slice_type type_ = Types.is_well_known Slice type_ || Types.is_well_known String_slice type_

let is_storage_type type_ =
  Types.is_well_known List type_ || Types.is_well_known Slice type_ || Types.is_builtin Array type_

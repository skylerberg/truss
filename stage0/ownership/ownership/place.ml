type root = Local of Core.local | Temporary of Mir.local | Constant of Path.t | Environment
type step = Field of string | Element of Core.origin | Range of Core.origin
type t = { root : root; steps : step list }
type overlap = Disjoint | Overlapping | Maybe_disjoint of Core.origin list * Core.origin list

let rec split_selection steps =
  match steps with
  | Range origin :: rest ->
      let origins, rest = split_selection rest in
      (origin :: origins, rest)
  | Element origin :: rest -> ([ origin ], rest)
  | Field _ :: _ | [] -> ([], steps)

let classify_overlap left right =
  if left.root <> right.root then Disjoint
  else
    let rec classify_steps left right =
      match (left, right) with
      | [], _ | _, [] -> Overlapping
      | Field first :: left, Field second :: right ->
          if first = second then classify_steps left right else Disjoint
      | (Element first | Range first) :: left_rest, (Element second | Range second) :: right_rest
        when first = second ->
          classify_steps left_rest right_rest
      | (Element _ | Range _) :: _, (Element _ | Range _) :: _ -> (
          let left_selection, left_rest = split_selection left
          and right_selection, right_rest = split_selection right in
          match classify_steps left_rest right_rest with
          | Disjoint -> Disjoint
          | Overlapping | Maybe_disjoint _ -> Maybe_disjoint (left_selection, right_selection))
      | _ :: left, _ :: right -> classify_steps left right
    in
    classify_steps left.steps right.steps

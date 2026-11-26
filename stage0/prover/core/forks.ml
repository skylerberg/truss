type exit = { exited : State.frame; exit_locals : Locals.local list }

type branch = {
  read : State.frame -> State.frame option * exit list;
  read_end : State.frame -> State.frame option;
  list_changed_parts : State.frame -> State.changed_part list;
}

type outcomes = { ended : State.frame option; exits : exit list }

let read_alone (frame : State.frame) branch =
  let ended, exits = branch.read (snd (Facts.suppose frame "branch")) in
  { ended; exits }

let read_end_of_every_branch (frame : State.frame) branches alone =
  if List.exists (fun outcomes -> Option.is_none outcomes.ended) alone then None
  else
    Option.map
      (fun (ended : State.frame) -> { ended with makes_obligations = frame.makes_obligations })
      (List.fold_left
         (fun after_earlier branch -> Option.bind after_earlier branch.read_end)
         (Some (snd (Facts.suppose { frame with makes_obligations = false } "ended")))
         branches)

let forget_changes (frame : State.frame) (changed : State.changed_part list) =
  let roots =
    List.sort_uniq compare
      (List.map (fun (part : State.changed_part) -> (part.root, part.declared_root_type)) changed)
  in
  Potentials.spend_forgotten roots ~before:frame ~after:(Loops.havoc frame changed)

let assume_an_outcome (frame : State.frame) (left : State.frame) parts outcomes =
  let amounts =
    List.map (fun (counter, _) -> (counter, Facts.declare_fresh left "spent" Logic.Int)) left.spent
  in
  let describe (at : State.frame) =
    Logic.conjunction
      (List.filter_map
         (fun part ->
           match (Encoding.find_changed_part left part, Encoding.find_changed_part at part) with
           | Some (_, value), Some (_, value_at) -> Some (Logic.equal value value_at)
           | _ -> None)
         parts
      @ List.map
          (fun (counter, amount) ->
            Logic.equal amount
              (Costs.since
                 ~start:(Counters.lookup_spent frame counter)
                 (Counters.lookup_spent at counter)))
          amounts)
  in
  Facts.assume left
    (Logic.disjunction
       (describe frame
       :: List.map (fun (at : State.frame) -> Logic.( &&& ) at.condition (describe at)) outcomes));
  Counters.spend left (fun counter ->
      Option.value (List.assoc_opt counter amounts) ~default:Costs.zero)

let leave_other_branches (frame : State.frame) others exit =
  let others =
    List.map
      (fun (branch, outcomes) ->
        ( List.filter
            (fun (part : State.changed_part) -> not (List.mem part.root exit.exit_locals))
            (branch.list_changed_parts exit.exited),
          Option.to_list outcomes.ended @ List.map (fun exit -> exit.exited) outcomes.exits ))
      others
  in
  let is_changed_by_one_branch (part : State.changed_part) =
    List.length
      (List.filter
         (fun (parts, _) ->
           List.exists (fun (other : State.changed_part) -> other.root = part.root) parts)
         others)
    = 1
  in
  List.fold_left
    (fun left (parts, outcomes) ->
      assume_an_outcome frame left (List.filter is_changed_by_one_branch parts) outcomes)
    (forget_changes exit.exited (List.concat_map fst others))
    others

let read (frame : State.frame) ~concurrent branches =
  let alone = List.map (read_alone frame) branches in
  let ended = read_end_of_every_branch frame branches alone in
  let with_outcomes = List.combine branches alone in
  let left =
    List.concat
      (List.mapi
         (fun index outcomes ->
           List.map
             (leave_other_branches frame
                (List.filteri (fun other _ -> other <> index) with_outcomes))
             outcomes.exits)
         alone)
  in
  let joined = Joins.join_frames (Option.to_list ended @ left) in
  if concurrent then Option.map Amounts.spend_wait_for_tasks joined else joined

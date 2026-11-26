let make_policy ~keeps_termination ~keeps_failures ~panic_condition : State.obligation_policy =
  { panic_condition; keeps_termination; keeps_failures }

let find_ruled_out_panic (context : State.context) (frame : State.frame) =
  if frame.panics then None else context.policy.panic_condition

let set_panics (frame : State.frame) ~panics = { frame with panics; can_declare_panic = false }

let make_obligation (context : State.context) (frame : State.frame) location obligation goal =
  Query.make_obligation context.query ~condition:frame.condition location obligation goal

let make_closed_obligation (context : State.context) (frame : State.frame) location obligation goal
    =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation context frame location obligation goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match Query.list_scope_facts context.query names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match Facts.close_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation context
             { frame with condition = Logic.Boolean true }
             location obligation closed)
    | None -> None

let is_panic_obligation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift | Panic -> true
  | _ -> false

let oblige ?cited ?(fixes = []) ?(can_be_required = true) ?(is_proven_by_evaluation = false)
    ?holds_when (context : State.context) (frame : State.frame) location obligation goal =
  let code = Catalog.Prover_description.find_code obligation in
  let holds_when = Option.value holds_when ~default:frame.obligation_condition in
  if
    (is_panic_obligation code && frame.panics)
    || (Option.is_some context.policy.panic_condition && not (is_panic_obligation code))
    || not
         (holds_when = context.condition
         || (code = Diagnostic.Code.Termination && context.policy.keeps_termination)
         || (is_panic_obligation code && context.policy.keeps_failures))
  then Facts.assume context frame goal
  else
    let is_held =
      match goal with
      | Logic.Boolean _ -> false
      | _ ->
          (not is_proven_by_evaluation) && frame.makes_obligations
          && (not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition))
          && Query.holds context.query ~under:frame.condition goal
    in
    if is_held then Facts.assume context frame goal
    else
      match
        make_closed_obligation context frame location obligation
          (Query.add_quantifier_facts context.query
             ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
             goal)
      with
      | Some obligation ->
          let is_home_body = Facts.is_home context frame.source && frame.makes_obligations in
          let fixes =
            match fixes with
            | [] when is_home_body && can_be_required -> (
                match Fixes.find_goal_code context goal with
                | Some _ when Logic.is_refuted goal -> []
                | Some required -> Fixes.add_requires context frame [ Clause required ]
                | None -> [])
            | fixes -> fixes
          in
          let fixes =
            if is_panic_obligation code && frame.can_declare_panic && is_home_body then
              fixes @ Fixes.make_panic_fix context
            else fixes
          in
          Query.add_obligation context.query { obligation with cited; fixes };
          Facts.assume context frame goal
      | None -> ()

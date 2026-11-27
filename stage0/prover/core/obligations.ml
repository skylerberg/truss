let make_policy ~keeps_termination ~keeps_failures ~panic_condition : State.obligation_policy =
  { panic_condition; keeps_termination; keeps_failures }

let find_ruled_out_panic (frame : State.frame) =
  if frame.panics then None else frame.environment.policy.panic_condition

let set_panics (frame : State.frame) ~panics = { frame with panics; can_declare_panic = false }

let make_obligation (frame : State.frame) location obligation goal =
  Query.make_obligation frame.query ~find_signature:Signatures.find_signature
    ~list_axioms:Signatures.list_axioms
    ~list_constructors:(Encoding.list_constructors frame.environment)
    ~condition:frame.condition location obligation goal

let make_closed_obligation (frame : State.frame) location obligation goal =
  if not frame.makes_obligations then None
  else if not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition) then
    Some (make_obligation frame location obligation goal)
  else
    let names = List.map (fun (name, _, _) -> name) frame.binders in
    let goal =
      match Query.list_scope_facts frame.query names with
      | [] -> goal
      | facts -> Logic.( ==> ) (Logic.conjunction facts) goal
    in
    match Facts.close_over_binders frame (Logic.( ==> ) frame.condition goal) with
    | Some closed ->
        Some
          (make_obligation { frame with condition = Logic.Boolean true } location obligation closed)
    | None -> None

let is_panic_obligation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift | Panic -> true
  | _ -> false

let oblige ?cited ?(fixes = []) ?(can_be_required = true) ?(is_proven_by_evaluation = false)
    ?holds_when (frame : State.frame) location obligation goal =
  let code = Catalog.Prover_description.find_code obligation in
  let holds_when = Option.value holds_when ~default:frame.obligation_condition in
  if
    (is_panic_obligation code && frame.panics)
    || (Option.is_some frame.environment.policy.panic_condition && not (is_panic_obligation code))
    || not
         (holds_when = frame.environment.condition
         || (code = Diagnostic.Code.Termination && frame.environment.policy.keeps_termination)
         || (is_panic_obligation code && frame.environment.policy.keeps_failures))
  then Facts.assume frame goal
  else
    let is_held =
      match goal with
      | Logic.Boolean _ -> false
      | _ ->
          (not is_proven_by_evaluation) && frame.makes_obligations
          && (not (Logic.mentions frame.bound goal || Logic.mentions frame.bound frame.condition))
          && Query.holds frame.query ~under:frame.condition goal
    in
    if is_held then Facts.assume frame goal
    else
      match
        make_closed_obligation frame location obligation
          (Query.add_quantifier_facts frame.query
             ~binders:(List.map (fun (name, _, _) -> name) frame.binders)
             goal)
      with
      | Some obligation ->
          let is_home_body = Facts.is_home frame && frame.makes_obligations in
          let fixes =
            match fixes with
            | [] when is_home_body && can_be_required -> (
                match Fixes.find_goal_code frame goal with
                | Some _ when Logic.is_refuted goal -> []
                | Some required -> Fixes.add_requires frame [ Clause required ]
                | None -> [])
            | fixes -> fixes
          in
          let fixes =
            if is_panic_obligation code && frame.can_declare_panic && is_home_body then
              fixes @ Fixes.make_panic_fix frame.environment
            else fixes
          in
          Query.add_obligation frame.query { obligation with cited; fixes };
          Facts.assume frame goal
      | None -> ()

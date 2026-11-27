let is_available (frame : State.frame) capability = Types.may_use capability frame.available

let find_ruled_out (frame : State.frame) =
  match frame.environment.policy.ruled_out with
  | Some ruled_out when not (is_available frame ruled_out.capability) -> Some ruled_out
  | Some _ | None -> None

let set_available (frame : State.frame) available = { frame with available; declared_uses = None }

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

let is_failing_operation : Diagnostic.Code.prover -> bool = function
  | Overflow | Division | Shift -> true
  | _ -> false

let find_guarded_capability (obligation : Catalog.Prover.obligation) code =
  match (obligation, code) with
  | (Precondition_may_use { capability; _ } | Uses_where_ruled_out { capability; _ }), _ ->
      Some capability
  | _, (Diagnostic.Code.Overflow | Division | Shift) -> Some (Types.Built_in Panic)
  | _, Termination -> Some (Types.Built_in Run_forever)
  | _ -> None

let oblige ?cited ?(fixes = []) ?(can_be_required = true) ?(is_proven_by_evaluation = false)
    ?holds_when (frame : State.frame) location obligation goal =
  let code = Catalog.Prover_description.find_code obligation in
  let holds_when = Option.value holds_when ~default:frame.obligation_condition in
  let guarded = find_guarded_capability obligation code in
  let policy = frame.environment.policy in
  let is_kept =
    match (policy.keeps, guarded) with
    | Every_capability, Some _ -> true
    | Capabilities kept, Some capability -> List.mem capability kept
    | _, None -> false
  in
  if
    (is_failing_operation code && is_available frame (Built_in Panic))
    || (match policy.ruled_out with
      | Some ruled_out -> guarded <> Some ruled_out.capability
      | None -> false)
    || not (holds_when = frame.environment.condition || is_kept)
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
            match (guarded, frame.declared_uses) with
            | Some capability, Some declared
              when (is_failing_operation code || code = Capability_condition)
                   && is_home_body
                   && not (Types.may_use capability declared) ->
                fixes @ Fixes.make_uses_fix frame.environment capability
            | _ -> fixes
          in
          Query.add_obligation frame.query { obligation with cited; fixes };
          Facts.assume frame goal
      | None -> ()

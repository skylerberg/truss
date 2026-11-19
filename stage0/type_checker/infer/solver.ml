type failure =
  | Unmet of Types.ty
  | Unmet_associated of (string * Types.ty * Types.ty)
  | Refused of int

type decision = Holds | Waits | Fails of failure

let read_cause_span : State.cause -> Source.Definition_span.t = function
  | Bound { at; _ } | Operator at | Method_call at | Loop at | Any_conversion { at; _ } -> at
  | Excluded _ -> State.raise_bug "a requirement of a set has no span of its own"

let describe_associated state type_ =
  match State.zonk state type_ with
  | Types.Projection { base; trait; name } ->
      Printf.sprintf "the `%s` of `%s` under `%s`" name (Types.show base)
        (Types.show_trait { trait with associated = [] })
  | zonked -> Printf.sprintf "`%s`" (Types.show zonked)

let report_unmet_bound (state : State.state) ~at ~of_type subject (bound : Types.trait_reference)
    ~associated =
  let needs =
    Printf.sprintf "%s needs `%s: %s`"
      (match of_type with
      | Some type_ -> Printf.sprintf "`%s`" (State.show state type_)
      | None -> "This")
      (Types.show subject) (Types.show_trait bound)
  in
  let frame = State.read_current_frame state in
  let is_slice = Types.is_well_known Slice subject || Types.is_well_known String_slice subject in
  let has_mut_self_method =
    match Interface.Definition.find_trait_interface state.lookups.interface bound.trait with
    | Some trait ->
        List.exists
          (fun (method_ : Types.trait_method) -> method_.method_receiver = Instance Mut)
          trait.methods
    | None -> false
  in
  match
    List.find_opt
      (fun (reported, reported_bound, _) -> Types.equal reported subject && reported_bound = bound)
      frame.reported_unmet_bounds
  with
  | Some (_, _, report) -> report
  | None ->
      let report =
        State.add_diagnostic state Unsatisfied_bound at
          (match associated with
          | None when is_slice && has_mut_self_method ->
              needs
              ^ ", which does not hold: a slice implements no trait with a `mut self` method. \
                 Generic code could call the method on a copy of the slice, and a copy views the \
                 same elements."
          | None -> needs ^ ", which does not hold."
          | Some (name, found, _) ->
              Printf.sprintf "%s, and its `%s` is `%s`." needs name (State.show state found))
      in
      frame.reported_unmet_bounds <- (subject, bound, report) :: frame.reported_unmet_bounds;
      report

let report_failure (state : State.state) (goal : State.goal) ?associated subject =
  let shown = State.normalize state subject in
  let does_not_implement trait =
    Printf.sprintf "`%s` does not implement `%s`" (Types.show shown)
      (Types.show_trait (Unify.zonk_trait state.unifier trait))
  in
  match (goal.cause, goal.requirement) with
  | Excluded reason, _ -> reason shown
  | Bound { at; of_type }, Implements bound ->
      report_unmet_bound state ~at ~of_type shown (Unify.zonk_trait state.unifier bound) ~associated
  | Operator at, Implements trait ->
      State.add_diagnostic state
        (if Option.is_some associated then Mismatch else No_impl)
        at
        (match associated with
        | Some (_, found, wanted) -> (
            match State.zonk state found with
            | Types.Projection _ ->
                Printf.sprintf "%s may differ from %s."
                  (String.capitalize_ascii (describe_associated state found))
                  (describe_associated state wanted)
            | found ->
                Printf.sprintf "This operator gives `%s`, and %s is expected." (Types.show found)
                  (describe_associated state wanted))
        | None -> does_not_implement trait ^ ", so the operator does not apply.")
  | (Method_call at | Loop at), Implements trait ->
      State.add_diagnostic state
        (match goal.cause with Loop _ -> Not_indexable | _ -> No_impl)
        at
        (does_not_implement trait ^ ".")
  | Any_conversion { at; any_type }, Implements trait ->
      State.add_diagnostic state No_impl at
        (match associated with
        | None -> does_not_implement trait ^ "."
        | Some (name, found, _) ->
            Printf.sprintf "`%s` is expected, and the `%s` of `%s` is `%s`." (Types.show any_type)
              name (Types.show shown) (State.show state found))
  | (Bound _ | Operator _ | Method_call _ | Loop _ | Any_conversion _), Within _ ->
      State.raise_bug "a goal's cause does not fit its requirement"

let fail (state : State.state) (goal : State.goal) failure =
  let report =
    match failure with
    | Unmet subject -> report_failure state goal subject
    | Unmet_associated associated -> report_failure state goal ~associated goal.subject
    | Refused root -> State.report_decided_in_specification state (read_cause_span goal.cause) root
  in
  List.iter (fun (_, output) -> ignore (State.unify state output (Types.Error report))) goal.outputs;
  report

let fail_unification (state : State.state) (goal : State.goal) =
  match state.unifier.refused_code_unknown with
  | Some root -> Fails (Refused root)
  | None -> Fails (Unmet goal.subject)

let make_goal (state : State.state) subject requirement ~outputs ~cause : State.goal =
  { subject; requirement; outputs; cause; is_specification = state.unifier.checks_specification }

let has_unknowns (state : State.state) arguments =
  List.exists (fun argument -> Unify.list_argument_unknowns state.unifier argument <> []) arguments

let unify_associated_types (state : State.state) (goal : State.goal) (trait : Types.trait_reference)
    find =
  match
    List.find_map
      (fun (name, expected) ->
        Option.bind (find name) (fun found ->
            if State.unify state found expected then None
            else Some (Unmet_associated (name, found, expected))))
      (trait.associated @ goal.outputs)
  with
  | Some failure -> Fails failure
  | None -> Holds

let project (state : State.state) subject wanted name =
  Interface.Impls.project_associated_type state.lookups.interface
    ~list_bounds:(State.lookup_bounds state) subject
    (Unify.zonk_trait state.unifier wanted)
    name

let narrow (state : State.state) goal variable set =
  if Unify.unify state.unifier variable (Unify.make_fresh_number state.unifier set) then begin
    state.narrowings <-
      {
        narrowed = variable;
        allowed = set;
        report_excluded = (fun excluded -> report_failure state goal excluded);
      }
      :: state.narrowings;
    Holds
  end
  else Fails (Unmet variable)

let decide_within state (goal : State.goal) set =
  match State.normalize state goal.subject with
  | Types.Error _ | Types.Hole -> Holds
  | Types.Variable _ as variable ->
      if Option.is_none (State.find_domain state variable) then Waits
      else narrow state goal variable set
  | resolved -> if State.is_within state resolved set then Holds else Fails (Unmet resolved)

let decide_by_bounds (state : State.state) goal trait ~subject ~(wanted : Types.trait_reference) =
  let matching =
    Interface.Impls.list_matching_bounds state.lookups.interface
      ~list_bounds:(State.lookup_bounds state) subject wanted
  in
  let decide_outputs () = unify_associated_types state goal trait (project state subject wanted) in
  if has_unknowns state wanted.trait_arguments then
    match
      List.sort_uniq compare
        (List.map (fun (bound : Types.trait_reference) -> bound.trait_arguments) matching)
    with
    | [ arguments ] ->
        if Unify.unify_arguments state.unifier wanted.trait_arguments arguments then
          decide_outputs ()
        else fail_unification state goal
    | _ -> Waits
  else if matching <> [] then decide_outputs ()
  else Fails (Unmet goal.subject)

let decide_number (state : State.state) (goal : State.goal) (trait : Types.trait_reference) ~subject
    ~(wanted : Types.trait_reference) domain =
  let covers domain implementors =
    List.for_all (fun member -> List.mem member implementors) domain
  in
  let narrowing =
    match Types.find_sealed_implementors wanted.trait with
    | Some implementors
      when List.exists (fun member -> List.mem member implementors) domain
           && not (covers domain implementors) ->
        narrow state goal subject implementors
    | _ -> Holds
  in
  let domain = Option.value ~default:domain (State.find_domain state subject) in
  let is_general type_ =
    match State.resolve state type_ with
    | Types.Variable _ -> Option.is_none (State.find_domain state type_)
    | _ -> false
  in
  let joins_without_narrowing (bound : Types.argument) (argument : Types.argument) =
    match (bound, argument) with
    | Types.Type bound, Types.Type argument ->
        is_general bound || is_general argument
        || Types.equal (State.zonk state bound) (State.zonk state argument)
    | _ -> bound = argument
  in
  let covering_bounds =
    List.sort_uniq compare
      (List.concat_map
         (fun sealed ->
           let path = Well_known.make_path sealed in
           match Types.find_sealed_implementors path with
           | Some implementors when covers domain implementors ->
               List.filter
                 (fun (bound : Types.trait_reference) -> Path.equal bound.trait wanted.trait)
                 (Interface.Properties.list_bound_closure state.lookups.interface ~self:subject
                    (State.make_trait_reference ~arguments:[] path))
           | _ -> [])
         Types.sealed_traits)
  in
  match (narrowing, covering_bounds) with
  | (Fails _ as failed), _ -> failed
  | _, [ bound ]
    when List.equal joins_without_narrowing bound.trait_arguments wanted.trait_arguments
         && List.for_all
              (fun (name, _) -> List.mem_assoc name bound.associated)
              (trait.associated @ goal.outputs) ->
      if Unify.unify_arguments state.unifier bound.trait_arguments wanted.trait_arguments then
        unify_associated_types state goal trait (fun name -> List.assoc_opt name bound.associated)
      else fail_unification state goal
  | _ -> Waits

let rec decide (state : State.state) ~depth (goal : State.goal) =
  match goal.requirement with
  | Within set -> decide_within state goal set
  | Implements trait -> decide_implements state ~depth goal trait

and decide_implements state ~depth goal trait =
  let subject = State.normalize state goal.subject in
  let wanted = State.normalize_trait state { trait with associated = [] } in
  let error =
    List.find_opt Types.is_error
      (subject
      :: List.filter_map
           (function Types.Type type_ -> Some type_ | Types.Value _ -> None)
           wanted.trait_arguments)
  in
  match
    ( subject,
      error,
      Interface.Definition.find_interface state.lookups.interface wanted.trait,
      Interface.Impls.decide_property_trait state.lookups.interface
        ~list_bounds:(State.lookup_bounds state) wanted.trait subject )
  with
  | Types.Hole, _, _, _ -> unify_associated_types state goal trait (fun _ -> Some subject)
  | _, Some error, _, _ -> unify_associated_types state goal trait (fun _ -> Some error)
  | _, None, Some (Interface.Environment.Error_interface report), _ ->
      unify_associated_types state goal trait (fun _ -> Some (Types.Error report))
  | _, None, _, Some (Holds | Depends_on (Types.Error _ | Types.Hole)) -> Holds
  | _, None, _, Some Fails -> Fails (Unmet goal.subject)
  | _, None, _, Some (Depends_on _) -> Waits
  | Types.Variable _, None, _, None -> (
      match State.find_domain state subject with
      | None -> Waits
      | Some domain -> decide_number state goal trait ~subject ~wanted domain)
  | Types.Named _, None, _, None ->
      if has_unknowns state wanted.trait_arguments then Waits
      else select state ~depth goal trait ~subject ~wanted
  | Types.Projection { base = Types.Variable _; _ }, None, _, None -> Waits
  | (Types.Parameter _ | Projection _ | Any _), None, _, None ->
      decide_by_bounds state goal trait ~subject ~wanted
  | (Types.Function _ | Never | Integer | Error _), None, _, None -> Fails (Unmet goal.subject)

and select state ~depth goal trait ~subject ~wanted =
  Interface.Impls.check_recursion_depth ~depth subject wanted;
  match Interface.Impls.select_impl state.lookups.interface subject wanted with
  | None -> Fails (Unmet goal.subject)
  | Some impl -> (
      let substitution =
        Types.make_substitution impl.impl_generics
          (State.make_fresh_generic_arguments state impl.impl_generics)
      in
      if
        not
          (Unify.unify_arguments state.unifier
             (Types.substitute_trait substitution impl.implements).trait_arguments
             wanted.trait_arguments
          && State.unify state (Types.substitute substitution impl.for_type) subject)
      then fail_unification state goal
      else
        let at = read_cause_span goal.cause in
        match
          List.find_map
            (fun (argument, bound) ->
              match
                decide state ~depth:(depth + 1)
                  (make_goal state argument (Implements bound) ~outputs:[]
                     ~cause:(Bound { at; of_type = None }))
              with
              | Holds -> None
              | decision -> Some decision)
            (Interface.Impls.list_required_bounds impl.impl_generics substitution)
        with
        | Some Waits -> Waits
        | Some (Fails _) -> Fails (Unmet goal.subject)
        | Some Holds | None ->
            unify_associated_types state goal trait (fun name ->
                match List.assoc_opt name impl.implements.associated with
                | Some chosen -> Some (Types.substitute substitution chosen)
                | None -> project state subject wanted name))

let add_goal (state : State.state) goal =
  match decide state ~depth:0 goal with
  | Holds -> None
  | Waits ->
      let frame = State.read_current_frame state in
      frame.goals <- goal :: frame.goals;
      None
  | Fails failure -> Some (fail state goal failure)

let require state cause ?(outputs = []) subject trait =
  ignore (add_goal state (make_goal state subject (Implements trait) ~outputs ~cause))

let require_within state subject set ~reason =
  match
    add_goal state (make_goal state subject (Within set) ~outputs:[] ~cause:(Excluded reason))
  with
  | Some report -> Types.Error report
  | None -> subject

let solve_frame (state : State.state) (frame : State.frame) =
  let enclosing = state.unifier.checks_specification in
  let rec loop () =
    let pending = frame.goals and narrowings = state.narrowings in
    frame.goals <-
      List.filter
        (fun (goal : State.goal) ->
          state.unifier.checks_specification <- goal.is_specification;
          match decide state ~depth:0 goal with
          | Waits -> true
          | Holds -> false
          | Fails failure ->
              ignore (fail state goal failure);
              false)
        pending;
    if
      List.compare_lengths frame.goals pending < 0
      || List.compare_lengths state.narrowings narrowings > 0
    then loop ()
  in
  loop ();
  state.unifier.checks_specification <- enclosing

let run_in_statement state env span body =
  State.run_in_statement state env span ~solve:(solve_frame state) body

type outcome = Solved | Waits | Failed of Diagnostic.reported

let rec find_root (goal : State.goal) =
  match goal.cause with Condition parent -> find_root parent | _ -> goal

let find_span (state : State.state) (goal : State.goal) =
  match (find_root goal).cause with
  | Bound { at; _ } | Method_call at | Loop at | Any_conversion { at; _ } -> at
  | Operator { call; _ } -> State.read_span state call
  | Excluded _ | Condition _ -> State.raise_bug "a requirement of a set has no span of its own"

let name_trait (trait : Types.trait_reference) =
  match trait.trait with Top { name; _ } -> name | path -> Path.show path

let describe_associated state type_ =
  match State.zonk state type_ with
  | Types.Projection { base; trait; name } ->
      Printf.sprintf "the `%s` of `%s` under `%s`" name (Types.show base)
        (Types.show_trait { trait with associated = [] })
  | zonked -> Printf.sprintf "`%s`" (Types.show zonked)

let report_unmet_bound (state : State.state) ~at ~of_type subject bound ~associated =
  let frame = State.find_current_frame state in
  match
    List.find_opt
      (fun (reported, reported_bound, _) -> Types.equal reported subject && reported_bound = bound)
      frame.reported_unmet_bounds
  with
  | Some (_, _, report) -> report
  | None ->
      let needs =
        Printf.sprintf "%s needs `%s: %s`"
          (match of_type with
          | Some type_ -> Printf.sprintf "`%s`" (State.show state type_)
          | None -> "This")
          (Types.show subject) (Types.show_trait bound)
      in
      let report =
        State.add_diagnostic state Unsatisfied_bound at
          (match associated with
          | None -> needs ^ ", which does not hold."
          | Some (name, found, _) ->
              Printf.sprintf "%s, and its `%s` is `%s`." needs name (State.show state found))
      in
      frame.reported_unmet_bounds <- (subject, bound, report) :: frame.reported_unmet_bounds;
      report

let report_failure (state : State.state) (goal : State.goal) ?associated subject =
  let root = find_root goal in
  let subject = if root == goal then subject else root.subject in
  let shown = State.normalize state subject in
  let show_trait trait = Types.show_trait (Unify.zonk_trait state.unifier trait) in
  match (root.cause, root.requirement) with
  | Excluded reason, _ -> reason shown
  | Bound { at; of_type }, Implements bound ->
      report_unmet_bound state ~at ~of_type shown (Unify.zonk_trait state.unifier bound) ~associated
  | Operator { call; left; right }, Implements trait -> (
      let at = State.read_span state call in
      match (associated, right, trait.trait_arguments) with
      | Some (_, found, wanted), _, _ ->
          State.add_diagnostic state Mismatch at
            (match State.zonk state found with
            | Types.Projection _ ->
                Printf.sprintf "%s may differ from %s."
                  (String.capitalize_ascii (describe_associated state found))
                  (describe_associated state wanted)
            | found ->
                Printf.sprintf "This operator gives `%s`, and %s is expected." (Types.show found)
                  (describe_associated state wanted))
      | None, Some right, [ Types.Type right_type ]
        when State.is_within state shown Types.integer_types
             && State.is_within state right_type Types.integer_types ->
          State.add_operand_mismatch state ~call ~left ~right ~left_type:subject ~right_type
      | None, _, _ ->
          State.add_diagnostic state No_impl at
            (Printf.sprintf "`%s` does not implement `%s`, so the operator does not apply."
               (Types.show shown) (show_trait trait)))
  | (Method_call at | Loop at), Implements trait ->
      State.add_diagnostic state
        (match root.cause with Loop _ -> Not_indexable | _ -> No_impl)
        at
        (Printf.sprintf "`%s` does not implement `%s`." (Types.show shown) (show_trait trait))
  | Any_conversion { at; any_type }, Implements trait ->
      State.add_diagnostic state No_impl at
        (match associated with
        | None ->
            Printf.sprintf "`%s` does not implement `%s`." (Types.show shown) (show_trait trait)
        | Some (name, found, _) ->
            Printf.sprintf "`%s` is expected, and the `%s` of `%s` is `%s`." (Types.show any_type)
              name (Types.show shown) (State.show state found))
  | (Bound _ | Operator _ | Method_call _ | Loop _ | Any_conversion _), Within _ | Condition _, _ ->
      State.raise_bug "a goal's cause does not fit its requirement"

let fail_unification (state : State.state) goal =
  match state.unifier.refused_code_unknown with
  | Some root -> Failed (State.report_decided_in_specification state (find_span state goal) root)
  | None -> Failed (report_failure state goal goal.subject)

let unify_associated_types (state : State.state) (goal : State.goal) (trait : Types.trait_reference)
    find =
  let rec unify_each = function
    | [] -> Solved
    | (name, expected) :: rest -> (
        match find name with
        | Some found when not (State.unify state found expected) ->
            Failed (report_failure state goal ~associated:(name, found, expected) goal.subject)
        | _ -> unify_each rest)
  in
  unify_each (trait.associated @ goal.outputs)

let project (state : State.state) subject wanted name =
  Interface.Impls.project_associated_type state.lookups.interface
    ~list_bounds:(State.lookup_bounds state) subject
    (Unify.zonk_trait state.unifier wanted)
    name

let rec add_goal (state : State.state) goal =
  let outcome = solve state goal in
  (match outcome with
  | Waits ->
      let frame = State.find_current_frame state in
      frame.goals <- goal :: frame.goals
  | Solved | Failed _ -> ());
  outcome

and solve (state : State.state) (goal : State.goal) =
  let enclosing = state.unifier.checks_specification in
  state.unifier.checks_specification <- goal.is_specification;
  let outcome =
    match goal.requirement with
    | Within set -> solve_within state goal set
    | Implements trait -> solve_implements state goal trait
  in
  state.unifier.checks_specification <- enclosing;
  (match outcome with
  | Failed report ->
      List.iter
        (fun (_, output) -> ignore (State.unify state output (Types.Error report)))
        (find_root goal).outputs
  | Solved | Waits -> ());
  outcome

and solve_within state goal set =
  match State.normalize state goal.subject with
  | Types.Error _ | Types.Hole -> Solved
  | Types.Variable index as variable -> (
      match Unify.find_domain state.unifier index with
      | None -> Waits
      | Some _ -> narrow state goal variable set)
  | resolved ->
      if State.is_within state resolved set then Solved
      else Failed (report_failure state goal resolved)

and narrow state goal variable set =
  if Unify.unify state.unifier variable (Unify.make_fresh_number state.unifier set) then begin
    state.narrowings <-
      {
        narrowed = variable;
        allowed = set;
        report_excluded = (fun excluded -> report_failure state goal excluded);
      }
      :: state.narrowings;
    Solved
  end
  else Failed (report_failure state goal variable)

and solve_implements state goal trait =
  let subject = State.normalize state goal.subject in
  let wanted = State.normalize_trait state { trait with associated = [] } in
  let lookups = state.lookups.interface in
  Interface.Impls.check_recursion_depth ~depth:goal.depth subject wanted;
  match
    ( subject,
      Interface.Definition.find_interface lookups wanted.trait,
      Interface.Impls.decide_property_trait lookups ~list_bounds:(State.lookup_bounds state)
        wanted.trait subject )
  with
  | (Types.Error _ | Types.Hole), _, _ ->
      unify_associated_types state goal trait (fun _ -> Some subject)
  | _, Some (Interface.Environment.Error_interface report), _ ->
      unify_associated_types state goal trait (fun _ -> Some (Types.Error report))
  | _, _, Some Holds -> Solved
  | _, _, Some Fails -> Failed (report_failure state goal goal.subject)
  | _, _, Some (Depends_on _) -> Waits
  | Types.Variable index, _, None -> (
      match Unify.find_domain state.unifier index with
      | None -> Waits
      | Some domain -> solve_number state goal trait ~subject ~wanted domain)
  | Types.Named { path; _ }, _, None ->
      if List.exists Types.is_unsolved_argument wanted.trait_arguments then Waits
      else select state goal trait ~subject ~wanted path
  | (Types.Parameter _ | Projection _ | Any _), _, None ->
      solve_by_bounds state goal trait ~subject ~wanted
  | (Types.Function _ | Never | Integer), _, None -> Failed (report_failure state goal goal.subject)

and solve_by_bounds state goal trait ~subject ~wanted =
  let matching =
    Interface.Impls.list_matching_bounds state.lookups.interface
      ~list_bounds:(State.lookup_bounds state) subject wanted
  in
  let decide () = unify_associated_types state goal trait (project state subject wanted) in
  if List.exists Types.is_unsolved_argument wanted.trait_arguments then
    match
      List.sort_uniq compare
        (List.map (fun (bound : Types.trait_reference) -> bound.trait_arguments) matching)
    with
    | [ arguments ] ->
        if Unify.unify_arguments state.unifier wanted.trait_arguments arguments then decide ()
        else fail_unification state goal
    | _ -> Waits
  else if matching <> [] then decide ()
  else Failed (report_failure state goal goal.subject)

and solve_number state goal trait ~subject ~wanted domain =
  let is_general type_ =
    match State.resolve state type_ with
    | Types.Variable index -> Option.is_none (Unify.find_domain state.unifier index)
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
      (List.filter
         (fun (bound : Types.trait_reference) -> Path.equal bound.trait wanted.trait)
         (List.concat_map
            (fun (sealed, implementors) ->
              if List.for_all (fun member -> List.mem member implementors) domain then
                Interface.Properties.list_bound_closure state.lookups.interface ~self:subject
                  (State.make_trait_reference ~arguments:[] (Well_known.make_path sealed))
              else [])
            Types.sealed_traits))
  in
  match (covering_bounds, Types.find_integer_implementors wanted.trait) with
  | [ bound ], _
    when List.length bound.trait_arguments = List.length wanted.trait_arguments
         && List.for_all2 joins_without_narrowing bound.trait_arguments wanted.trait_arguments
         && List.for_all
              (fun (name, _) -> List.mem_assoc name bound.associated)
              ((trait : Types.trait_reference).associated @ goal.outputs) ->
      if Unify.unify_arguments state.unifier bound.trait_arguments wanted.trait_arguments then
        unify_associated_types state goal trait (fun name -> List.assoc_opt name bound.associated)
      else fail_unification state goal
  | _, Some implementors when List.exists (fun member -> List.mem member implementors) domain -> (
      match narrow state goal subject implementors with
      | Solved -> solve_implements state goal trait
      | outcome -> outcome)
  | _ -> Waits

and select state goal trait ~subject ~wanted path =
  match Interface.Impls.select_impl state.lookups.interface ~head:path wanted with
  | None -> Failed (report_failure state goal goal.subject)
  | Some (impl, matched) -> (
      let substitution =
        List.fold_left
          (fun substitution (generic : Types.generic) ->
            match Types.find_argument generic.generic substitution with
            | Some _ -> substitution
            | None ->
                Types.bind_argument generic.generic
                  (State.make_fresh_argument state generic)
                  substitution)
          matched impl.impl_generics
      in
      if not (State.unify state (Types.substitute substitution impl.for_type) subject) then
        fail_unification state goal
      else
        match
          unify_associated_types state goal trait (fun name ->
              match List.assoc_opt name impl.implements.associated with
              | Some chosen -> Some (Types.substitute substitution chosen)
              | None -> project state subject wanted name)
        with
        | Solved ->
            List.iter
              (fun (argument, bound) ->
                ignore
                  (add_goal state
                     {
                       subject = argument;
                       requirement = Implements bound;
                       outputs = [];
                       cause = Condition goal;
                       depth = goal.depth + 1;
                       is_specification = goal.is_specification;
                     }))
              (Interface.Impls.list_required_bounds impl.impl_generics substitution);
            Solved
        | outcome -> outcome)

let make_goal (state : State.state) subject requirement ~outputs ~cause : State.goal =
  {
    subject;
    requirement;
    outputs;
    cause;
    depth = 0;
    is_specification = state.unifier.checks_specification;
  }

let require state cause ?(outputs = []) subject trait =
  ignore (add_goal state (make_goal state subject (Implements trait) ~outputs ~cause))

let require_within state subject set ~reason =
  match
    add_goal state (make_goal state subject (Within set) ~outputs:[] ~cause:(Excluded reason))
  with
  | Failed report -> Types.Error report
  | Solved | Waits -> subject

let solve_frame state (frame : State.frame) =
  let rec loop () =
    let pending = List.rev frame.goals in
    frame.goals <- [];
    let waiting =
      List.filter
        (fun goal -> match solve state goal with Waits -> true | Solved | Failed _ -> false)
        pending
    in
    frame.goals <- frame.goals @ List.rev waiting;
    if List.length waiting < List.length pending then loop ()
  in
  loop ()

let describe_pending (cause : State.cause) trait =
  match cause with
  | Loop _ ->
      Printf.sprintf
        "This loop does not determine the arguments of `%s`, whose methods give its elements."
        (name_trait trait)
  | _ ->
      Printf.sprintf
        "This call does not determine the arguments of `%s`. Write the call in full with them."
        (name_trait trait)

let report_unsolved (state : State.state) (frame : State.frame) =
  match State.list_unsolved state frame with
  | [] -> ()
  | unsolved ->
      let list_trait_unknowns (trait : Types.trait_reference) =
        List.concat_map (Unify.list_argument_unknowns state.unifier) trait.trait_arguments
      in
      let undetermined =
        List.filter_map
          (fun (goal : State.goal) ->
            match (goal.cause, goal.requirement) with
            | (Method_call at | Loop at), Implements trait
              when (not (Types.contains_unsolved (State.zonk state goal.subject)))
                   && List.exists
                        (fun unknown -> List.mem unknown unsolved)
                        (list_trait_unknowns trait) ->
                Some (at, goal.cause, trait)
            | _ -> None)
          (List.rev frame.goals)
      in
      let reports =
        List.map
          (fun (at, cause, trait) ->
            State.add_diagnostic state Cannot_infer at (describe_pending cause trait))
          undetermined
      in
      let explained =
        List.concat_map (fun (_, _, trait) -> list_trait_unknowns trait) undetermined
      in
      let report =
        match reports with
        | first :: _ when List.for_all (fun unknown -> List.mem unknown explained) unsolved -> first
        | _ ->
            State.add_diagnostic state Cannot_infer frame.span
              "The types in this statement cannot be inferred from it alone. Give the `let` a \
               type, or the call type arguments, such as `var names: List[String] = []`."
      in
      if Option.is_none state.unsolved then state.unsolved <- Some report;
      List.iter
        (function
          | Unify.Unknown_type index ->
              Hashtbl.replace state.unifier.type_solutions index (Types.Error report)
          | Unknown_value _ -> ())
        unsolved;
      frame.goals <- []

let run_in_statement (state : State.state) env span body =
  let enclosing = state.unifier.checks_specification in
  let frame = State.open_frame state env span in
  let result = body () in
  State.constrain_capability_equalities state frame;
  solve_frame state frame;
  State.give_defaults state frame;
  solve_frame state frame;
  report_unsolved state frame;
  State.close_frame state frame;
  state.unifier.checks_specification <- enclosing;
  result

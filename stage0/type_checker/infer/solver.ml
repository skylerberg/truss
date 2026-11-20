type failure = Unmet | Unmet_associated of (string * Types.ty * Types.ty) | Refused of int
type decision = Holds | Waits | Fails of failure | Becomes of State.goal list

let read_cause_span : State.cause -> Source.Definition_span.t = function
  | Bound { at; _ } | Operator { at; _ } | Method_call at | Loop at | Any_conversion { at; _ } -> at
  | Excluded _ -> State.raise_bug "a requirement of a set has no span of its own"

let describe_associated state type_ =
  match State.zonk state type_ with
  | Types.Projection { base; trait; name } ->
      Printf.sprintf "the `%s` of `%s` under `%s`" name (Types.show base)
        (Types.show_trait { trait with associated = [] })
  | zonked -> Printf.sprintf "`%s`" (Types.show zonked)

let report_unmet_bound (state : State.state) ~at ~of_type ~sides ~unmet subject
    (bound : Types.trait_reference) ~associated =
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
        State.add_mismatch_diagnostic state Unsatisfied_bound at ~sides
          ((match associated with
             | None when is_slice && has_mut_self_method ->
                 needs
                 ^ ", which does not hold: a slice implements no trait with a `mut self` method. \
                    Generic code could call the method on a copy of the slice, and a copy views \
                    the same elements."
             | None -> needs ^ ", which does not hold."
             | Some (name, found, _) ->
                 Printf.sprintf "%s, and its `%s` is `%s`." needs name (State.show state found))
          ^ unmet)
      in
      frame.reported_unmet_bounds <- (subject, bound, report) :: frame.reported_unmet_bounds;
      report

let report_requirement (state : State.state) (goal : State.goal) ?associated ~unmet subject =
  let shown = State.normalize state subject in
  let does_not_implement trait =
    Printf.sprintf "`%s` does not implement `%s`" (Types.show shown)
      (Types.show_trait (Unify.zonk_trait state.unifier trait))
  in
  match (goal.cause, goal.requirement) with
  | Excluded reason, _ -> reason shown
  | Bound { at; of_type }, Implements bound ->
      let bound = Unify.zonk_trait state.unifier bound in
      let meets member =
        Option.is_some (State.find_evidence state (Types.make_builtin member) bound)
      in
      let sides =
        match goal.subject with
        | Types.Variable index ->
            List.filter_map
              (fun member ->
                if meets member then Some (goal.subject, Types.make_builtin member) else None)
              (Option.value ~default:[]
                 (Unify.find_domain state.unifier (Unify.read_root state.unifier index)))
        | _ -> []
      in
      report_unmet_bound state ~at ~of_type ~sides ~unmet shown bound ~associated
  | ( Operator { at; operands = Some (left, right) },
      Implements { trait_arguments = [ Types.Type argument ]; _ } )
    when Option.is_none associated && unmet = ""
         && State.is_within state goal.subject Types.number_types
         && State.is_within state argument Types.number_types ->
      State.add_operand_mismatch state ~at ~left:(left, goal.subject) ~right:(right, argument)
  | Operator { at; _ }, Implements trait ->
      State.add_diagnostic state
        (if Option.is_some associated then Mismatch else No_impl)
        at
        ((match associated with
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
        ^ unmet)
  | (Method_call at | Loop at), Implements trait ->
      State.add_diagnostic state
        (match goal.cause with Loop _ -> Not_indexable | _ -> No_impl)
        at
        (does_not_implement trait ^ "." ^ unmet)
  | Any_conversion { at; any_type }, Implements trait ->
      State.add_diagnostic state No_impl at
        ((match associated with
           | None -> does_not_implement trait ^ "."
           | Some (name, found, _) ->
               Printf.sprintf "`%s` is expected, and the `%s` of `%s` is `%s`."
                 (Types.show any_type) name (Types.show shown) (State.show state found))
        ^ unmet)
  | (Bound _ | Operator _ | Method_call _ | Loop _ | Any_conversion _), Within _ ->
      State.raise_bug "a goal's cause does not fit its requirement"

let report_failure (state : State.state) (goal : State.goal) ?associated subject =
  match (goal.needed_by, goal.requirement) with
  | None, _ -> report_requirement state goal ?associated ~unmet:"" subject
  | Some root, Implements condition ->
      report_requirement state root root.subject
        ~unmet:
          (Printf.sprintf " Its impl needs `%s: %s`." (State.show state subject)
             (Types.show_trait (Unify.zonk_trait state.unifier condition)))
  | Some _, Within _ -> State.raise_bug "an impl's condition is a set of types"

let list_goal_arguments (goal : State.goal) =
  match goal.requirement with
  | Implements trait -> Types.Type goal.subject :: trait.trait_arguments
  | Within _ -> [ Types.Type goal.subject ]

let fail (state : State.state) (goal : State.goal) failure =
  let report =
    match failure with
    | Unmet -> report_failure state goal goal.subject
    | Unmet_associated associated -> report_failure state goal ~associated goal.subject
    | Refused root -> State.report_decided_in_specification state (read_cause_span goal.cause) root
  in
  List.iter (fun (_, output) -> ignore (State.unify state output (Types.Error report))) goal.outputs;
  List.iter
    (fun (root, _) -> Hashtbl.replace state.unifier.type_solutions root (Types.Error report))
    (List.concat_map
       (function
         | Types.Type type_ -> State.list_class_pairs state (type_, type_) | Types.Value _ -> [])
       (list_goal_arguments goal));
  report

let fail_unification (state : State.state) =
  match state.unifier.refused_code_unknown with
  | Some root -> Fails (Refused root)
  | None -> Fails Unmet

let make_goal (state : State.state) subject requirement ~outputs ~cause : State.goal =
  { subject; requirement; outputs; cause; mode = state.unifier.mode; depth = 0; needed_by = None }

let has_unknowns (state : State.state) arguments =
  List.exists (fun argument -> Unify.list_argument_unknowns state.unifier argument <> []) arguments

let rec flatten_into (state : State.state) cause ~projections ~add type_ =
  Types.map
    (function
      | Types.Projection { base; trait; name } as projection
        when has_unknowns state [ Types.Type projection ] ->
          Some
            (match List.assoc_opt projection !projections with
            | Some output -> output
            | None ->
                let flatten = flatten_into state cause ~projections ~add in
                let output = State.make_fresh_type state in
                projections := (projection, output) :: !projections;
                let goal =
                  make_goal state (flatten base)
                    (Implements (Types.map_trait flatten trait))
                    ~outputs:[ (name, output) ]
                    ~cause
                in
                add goal;
                output)
      | _ -> None)
    type_

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
  match variable with
  | Types.Variable member
    when Unify.unify state.unifier variable (Unify.make_fresh_number state.unifier set) ->
      State.record_narrowing state member ~allowed:set ~report_excluded:(fun excluded ->
          report_requirement state goal ~unmet:"" excluded);
      Holds
  | _ -> Fails Unmet

let decide_within state (goal : State.goal) set =
  match State.normalize state goal.subject with
  | Types.Error _ | Types.Hole -> Holds
  | Types.Variable _ as variable ->
      if Option.is_none (State.find_domain state variable) then Waits
      else narrow state goal variable set
  | resolved -> if State.is_within state resolved set then Holds else Fails Unmet

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
        else fail_unification state
    | _ -> Waits
  else if matching <> [] then decide_outputs ()
  else Fails Unmet

let list_sealed_closures (state : State.state) subject ~includes =
  List.filter_map
    (fun sealed ->
      let path = Well_known.make_path sealed in
      match Types.find_sealed_implementors path with
      | Some implementors when includes implementors ->
          let trait = Types.make_trait_reference ~arguments:[] path in
          Some
            ( trait,
              Interface.Properties.list_bound_closure state.lookups.interface ~self:subject trait )
      | _ -> None)
    Types.sealed_traits

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
      (List.filter
         (fun (bound : Types.trait_reference) -> Path.equal bound.trait wanted.trait)
         (List.concat_map snd (list_sealed_closures state subject ~includes:(covers domain))))
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
      else fail_unification state
  | _ -> Waits

let select (state : State.state) (goal : State.goal) trait ~subject
    ~(wanted : Types.trait_reference) =
  Interface.Impls.check_recursion_depth ~depth:goal.depth subject wanted;
  match Interface.Impls.list_matching_impls state.lookups.interface subject wanted with
  | [] -> Fails Unmet
  | { impl; substitution; _ } :: _ -> (
      let unbound =
        List.filter
          (fun (generic : Types.generic) ->
            Option.is_none (Types.find_argument generic.generic substitution))
          impl.impl_generics
      in
      let substitution =
        Types.combine_substitutions substitution
          (Types.make_substitution unbound (State.make_fresh_generic_arguments state unbound))
      in
      if
        not
          (Unify.unify_arguments state.unifier
             (Types.substitute_trait substitution impl.implements).trait_arguments
             wanted.trait_arguments
          && State.unify state (Types.substitute substitution impl.for_type) subject)
      then fail_unification state
      else
        let conditions = ref [] in
        let add (condition : State.goal) =
          conditions :=
            {
              condition with
              depth = goal.depth + 1;
              needed_by = Some (Option.value goal.needed_by ~default:goal);
            }
            :: !conditions
        in
        let cause : State.cause = Bound { at = read_cause_span goal.cause; of_type = None } in
        let flatten = flatten_into state cause ~projections:(ref []) ~add in
        List.iter
          (fun (argument, bound) ->
            add
              (make_goal state (flatten argument)
                 (Implements (Types.map_trait flatten bound))
                 ~outputs:[] ~cause))
          (Interface.Impls.list_required_bounds impl.impl_generics substitution);
        match
          unify_associated_types state goal trait (fun name ->
              match List.assoc_opt name impl.implements.associated with
              | Some chosen -> Some (flatten (Types.substitute substitution chosen))
              | None -> project state subject wanted name)
        with
        | Holds -> Becomes (List.rev !conditions)
        | decision -> decision)

let decide_implements state (goal : State.goal) trait =
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
  | _, None, _, Some Fails -> Fails Unmet
  | _, None, _, Some (Depends_on _) -> Waits
  | Types.Variable _, None, _, None -> (
      match State.find_domain state subject with
      | None -> Waits
      | Some domain -> decide_number state goal trait ~subject ~wanted domain)
  | Types.Named _, None, _, None ->
      if has_unknowns state wanted.trait_arguments then Waits
      else select state goal trait ~subject ~wanted
  | (Types.Parameter _ | Projection _ | Any _), None, _, None ->
      decide_by_bounds state goal trait ~subject ~wanted
  | (Types.Function _ | Never | Integer | Error _), None, _, None -> Fails Unmet

let decide (state : State.state) (goal : State.goal) =
  match goal.requirement with
  | Within set -> decide_within state goal set
  | Implements trait -> decide_implements state goal trait

let rec add_goal (state : State.state) goal =
  match decide state goal with
  | Holds -> None
  | Waits ->
      state.goals <- goal :: state.goals;
      None
  | Fails failure -> Some (fail state goal failure)
  | Becomes conditions ->
      List.iter (fun condition -> ignore (add_goal state condition)) conditions;
      None

let flatten state cause ?(projections = ref []) type_ =
  flatten_into state cause ~projections ~add:(fun goal -> ignore (add_goal state goal)) type_

let require state cause ?(outputs = []) ?projections subject trait =
  let flatten = flatten state cause ?projections in
  let subject = flatten subject in
  ignore
    (add_goal state
       (make_goal state subject (Implements (Types.map_trait flatten trait)) ~outputs ~cause))

let resolve_associated_type state type_ (trait : Types.trait_reference) associated ~at =
  let name = Well_known.show_associated associated in
  match
    State.normalize state
      (flatten state
         (Bound { at; of_type = None })
         (Types.Projection { base = type_; trait; name }))
  with
  | Types.Projection { base = Types.Parameter _ | Types.Projection _; _ } as rigid -> rigid
  | Types.Projection { base; _ } ->
      State.raise_bug "`%s` gives no `%s` as a `%s`, and its evidence was found" (Types.show base)
        name (Types.show_trait trait)
  | resolved -> resolved

let require_within state subject set ~reason =
  match
    add_goal state (make_goal state subject (Within set) ~outputs:[] ~cause:(Excluded reason))
  with
  | Some report -> Types.Error report
  | None -> subject

let solve (state : State.state) ~selects =
  let rec loop () =
    let pending = state.goals and count = Unify.count_solutions state.unifier in
    state.goals <- [];
    let retained =
      List.filter
        (fun (goal : State.goal) ->
          (not (selects goal))
          || State.with_mode state goal.mode (fun () ->
              match decide state goal with
              | Waits -> true
              | Holds -> false
              | Fails failure ->
                  ignore (fail state goal failure);
                  false
              | Becomes conditions ->
                  List.iter (fun condition -> ignore (add_goal state condition)) conditions;
                  false))
        pending
    in
    state.goals <- retained @ state.goals;
    if List.compare_lengths retained pending < 0 || Unify.count_solutions state.unifier <> count
    then loop ()
  in
  loop ()

let solve_all state = solve state ~selects:(fun _ -> true)

let list_goal_inputs (state : State.state) (goal : State.goal) =
  List.concat_map (Unify.list_argument_unknowns state.unifier) (list_goal_arguments goal)

let gives (state : State.state) index (goal : State.goal) =
  List.exists (fun (_, output) -> State.resolve state output = Types.Variable index) goal.outputs

let rec walk_givers (state : State.state) (givers, waited) = function
  | Unify.Unknown_type index :: unknowns -> (
      match List.filter (gives state index) state.goals with
      | [] when Unify.may_decide state.unifier index ->
          walk_givers state (givers, Types.Variable index :: waited) unknowns
      | found ->
          let found = List.filter (fun goal -> not (List.memq goal givers)) found in
          walk_givers state
            (found @ givers, waited)
            (List.concat_map (list_goal_inputs state) found @ unknowns))
  | Unify.Unknown_value _ :: unknowns -> walk_givers state (givers, waited) unknowns
  | [] -> (givers, waited)

let make_default_type domain =
  match
    List.filter
      (fun default -> List.mem default domain)
      [ Language.Builtin_type.Integer; Int64; UInt64; Float64 ]
  with
  | Integer :: _ -> Types.Integer
  | default :: _ -> Types.make_builtin default
  | [] -> State.raise_bug "a number has no default type"

let default_quietly (state : State.state) type_ =
  Option.iter
    (fun domain -> ignore (Unify.unify state.unifier type_ (make_default_type domain)))
    (State.find_domain state type_)

let record_decisions (state : State.state) ~at =
  List.iter
    (fun root ->
      match State.resolve state (Types.Variable root) with
      | Types.Variable _ | Types.Error _ -> ()
      | decided_type -> State.record_decided state root ~site:Use ~decided_type ~at)
    (List.sort_uniq compare
       (List.map (Unify.read_root state.unifier) state.unifier.decided_numbers));
  state.unifier.decided_numbers <- []

let decide_default (state : State.state) ~site ~at type_ =
  match (State.resolve state type_, State.find_domain state type_) with
  | Types.Variable root, Some domain -> (
      let default = make_default_type domain in
      record_decisions state ~at:(State.read_current_frame state).span;
      ignore (Unify.unify state.unifier type_ default);
      state.unifier.decided_numbers <- [];
      match State.find_refused_class state ~sides:[ (type_, default) ] with
      | Some refused -> Types.Error (State.report_decided_in_specification state at refused)
      | None ->
          State.record_decided state root ~site ~decided_type:default ~at;
          default)
  | _ -> type_

let solve_head (state : State.state) ?default_at index =
  let solve_givers () =
    match walk_givers state ([], []) [ Unify.Unknown_type index ] with
    | [], _ -> ()
    | givers, _ -> solve state ~selects:(fun goal -> List.memq goal givers)
  in
  solve_givers ();
  match (default_at, walk_givers state ([], []) [ Unify.Unknown_type index ]) with
  | Some at, (_ :: _, waited) ->
      let count = Unify.count_solutions state.unifier in
      List.iter (fun input -> ignore (decide_default state ~site:Actual_head ~at input)) waited;
      if Unify.count_solutions state.unifier <> count then solve_givers ()
  | _ -> ()

let compare_in_source_order state left right =
  let left : Source.Definition_span.t = State.read_span state left
  and right : Source.Definition_span.t = State.read_span state right in
  compare (left.start, -left.stop) (right.start, -right.stop)

let settle (state : State.state) (frame : State.frame) =
  List.iter
    (fun (left, right) ->
      let report_missing _ =
        State.report state Mismatch frame.span
          (Printf.sprintf
             "Two function types here must use the same capabilities, and one uses `%s` where the \
              other uses `%s`."
             (Types.show_capabilities (State.resolve_capabilities state left))
             (Types.show_capabilities (State.resolve_capabilities state right)))
      in
      state.capability_constraints <-
        { subset = left; restriction = None; superset = right; report_missing }
        :: { subset = right; restriction = None; superset = left; report_missing }
        :: state.capability_constraints)
    state.unifier.deferred_capability_equalities;
  state.unifier.deferred_capability_equalities <- [];
  solve_all state;
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  let is_owned = function
    | Unify.Unknown_type index | Unknown_value index ->
        index >= frame.first_variable && Option.is_none (Unify.find_domain state.unifier index)
  in
  let list_output_unknowns (goal : State.goal) =
    List.concat_map (fun (_, output) -> Unify.list_unknowns state.unifier output) goal.outputs
  in
  (match parent with
  | Some _ ->
      List.iter
        (fun input -> ignore (decide_default state ~site:Statement_end ~at:frame.span input))
        (snd
           (walk_givers state ([], [])
              (List.filter is_owned (List.concat_map list_output_unknowns state.goals))))
  | None ->
      let rec default_goal_inputs () =
        let count = Unify.count_solutions state.unifier in
        List.iter (default_quietly state)
          (snd (walk_givers state ([], []) (List.concat_map (list_goal_inputs state) state.goals)));
        if Unify.count_solutions state.unifier <> count then begin
          solve_all state;
          default_goal_inputs ()
        end
      in
      default_goal_inputs ();
      Hashtbl.iter
        (fun index _ -> default_quietly state (Types.Variable index))
        state.unifier.domains);
  solve_all state;
  let list_types ids table = List.filter_map (fun id -> table.(id)) ids in
  let list_all_types () =
    list_types frame.recorded_expressions state.tables.types
    @ list_types frame.bindings state.tables.local_types
  in
  let list_call_arguments () =
    List.concat_map
      (fun id ->
        match state.tables.calls.(id) with
        | Some { callee = Trait_method { trait; instantiation; _ }; _ } ->
            trait.trait_arguments @ instantiation.type_arguments
        | Some
            {
              callee =
                ( Function { instantiation = { type_arguments; _ }; _ }
                | Constructor { type_arguments; _ }
                | Intrinsic { type_arguments; _ } );
              _;
            } ->
            type_arguments
        | _ -> [])
      frame.recorded_expressions
  in
  let list_goal_unknowns goal = list_goal_inputs state goal @ list_output_unknowns goal in
  let list_unknowns () =
    List.concat_map (Unify.list_unknowns state.unifier) (list_all_types ())
    @ List.concat_map (Unify.list_argument_unknowns state.unifier) (list_call_arguments ())
    @ List.concat_map list_goal_unknowns state.goals
  in
  let unsolved = List.filter is_owned (list_unknowns ()) in
  if unsolved <> [] then begin
    let list_trait_unknowns (trait : Types.trait_reference) =
      List.concat_map (Unify.list_argument_unknowns state.unifier) trait.trait_arguments
    in
    let undetermined =
      List.filter_map
        (fun (goal : State.goal) ->
          match (goal.cause, goal.requirement) with
          | ((Method_call at | Loop at) as cause), Implements trait
            when (not (Types.contains_unsolved (State.zonk state goal.subject)))
                 && List.exists
                      (fun unknown -> List.mem unknown unsolved)
                      (list_trait_unknowns trait) ->
              Some
                ( State.add_diagnostic state Cannot_infer at
                    (Printf.sprintf
                       (match cause with
                       | Loop _ ->
                           "This loop does not determine the arguments of `%s`, whose methods give \
                            its elements."
                       | _ ->
                           "This call does not determine the arguments of `%s`. Write the call in \
                            full with them.")
                       (match trait.trait with Top { name; _ } -> name | path -> Path.show path)),
                  list_trait_unknowns trait )
          | _ -> None)
        state.goals
    in
    let explained = List.concat_map snd undetermined in
    let report =
      match undetermined with
      | (first, _) :: _ when List.for_all (fun unknown -> List.mem unknown explained) unsolved ->
          first
      | _ ->
          State.add_diagnostic state Cannot_infer frame.span
            "The types in this statement cannot be inferred from it alone. Give the `let` a type, \
             or the call type arguments, such as `var names: List[String] = []`."
    in
    if Option.is_none state.unsolved then state.unsolved <- Some report;
    let reported_goals =
      List.filter
        (fun goal ->
          List.exists (fun unknown -> List.mem unknown unsolved) (list_goal_unknowns goal))
        state.goals
    in
    List.iter
      (function
        | Unify.Unknown_type index ->
            Hashtbl.replace state.unifier.type_solutions index (Types.Error report)
        | Unknown_value _ -> ())
      unsolved;
    solve_all state;
    state.goals <- List.filter (fun goal -> not (List.memq goal reported_goals)) state.goals
  end;
  (match parent with
  | Some _ -> record_decisions state ~at:frame.span
  | None -> state.unifier.decided_numbers <- []);
  let is_open unknown = not (is_owned unknown) in
  let finish table ids keep =
    List.iter
      (fun id ->
        match table.(id) with
        | Some type_ -> (
            let type_ = State.normalize state type_ in
            table.(id) <- Some type_;
            if List.exists is_open (Unify.list_unknowns state.unifier type_) then
              match parent with Some parent -> keep parent id | None -> ())
        | None -> ())
      ids
  in
  finish state.tables.types frame.recorded_expressions (fun (parent : State.frame) id ->
      parent.recorded_expressions <- id :: parent.recorded_expressions);
  finish state.tables.local_types frame.bindings (fun (parent : State.frame) id ->
      parent.bindings <- id :: parent.bindings);
  let is_settled table id =
    match table.(id) with
    | Some type_ -> not (List.exists is_open (Unify.list_unknowns state.unifier type_))
    | None -> true
  in
  let settled_bindings, open_bindings =
    List.partition (is_settled state.tables.local_types) (List.rev frame.compiled_bindings)
  in
  let settled_expressions, open_expressions =
    List.partition (is_settled state.tables.types) (List.rev frame.compiled_expressions)
  in
  Option.iter
    (fun (parent : State.frame) ->
      parent.compiled_bindings <- List.rev_append open_bindings parent.compiled_bindings;
      parent.compiled_expressions <- List.rev_append open_expressions parent.compiled_expressions)
    parent;
  List.iter (State.check_compiled_binding state) settled_bindings;
  List.iter
    (State.check_compiled_expression state)
    (List.sort (compare_in_source_order state) settled_expressions);
  if Option.is_none parent && state.goals <> [] then
    State.raise_bug "a goal is pending at the end of the definition"

let run_in_statement (state : State.state) (env : State.env) span body =
  let frame : State.frame =
    {
      first_variable = state.unifier.next + 1;
      recorded_expressions = [];
      bindings = [];
      reported_unmet_bounds = [];
      compiled_expressions = [];
      compiled_bindings = [];
      specification_only_report = None;
      span;
    }
  in
  state.frames <- frame :: state.frames;
  let result =
    State.with_specification state env.specification (fun () ->
        let result = body () in
        settle state frame;
        result)
  in
  state.frames <- List.tl state.frames;
  result

let holds_class (state : State.state) root type_ =
  List.exists
    (function Unify.Unknown_type index | Unknown_value index -> index = root)
    (Unify.list_unknowns state.unifier type_)

let find_refused_class (state : State.state) ~sides =
  Option.bind state.unifier.refused_code_unknown (fun root ->
      if List.exists (fun (side, _) -> holds_class state root side) sides then Some root else None)

let report_decided_in_specification (state : State.state) span root =
  let message =
    match
      Array.find_index
        (Option.fold ~none:false ~some:(holds_class state root))
        state.tables.local_types
    with
    | Some local ->
        let name = State.quote_span state (State.read_span state local) in
        Printf.sprintf "A specification cannot decide the type of `%s`. Declare `%s` with a type."
          name name
    | None ->
        "A specification cannot decide a type that code computes with. Give the call its type \
         arguments."
  in
  let report = State.add_diagnostic state Decided_in_specification span message in
  Unify.poison state.unifier root report;
  report

let rec list_class_pairs (state : State.state) (side, wanted) =
  match (side, State.resolve state wanted) with
  | Types.Variable index, _
    when Option.is_some (Unify.find_domain state.unifier (Unify.read_root state.unifier index)) ->
      [ (Unify.read_root state.unifier index, wanted) ]
  | Types.Variable _, _ when State.resolve state side <> side ->
      list_class_pairs state (State.resolve state side, wanted)
  | ( Types.Named { path; arguments },
      Types.Named { path = wanted_path; arguments = wanted_arguments } )
    when Path.equal path wanted_path && List.compare_lengths arguments wanted_arguments = 0 ->
      List.concat
        (List.map2
           (fun argument wanted_argument ->
             match (argument, wanted_argument) with
             | Types.Type argument, Types.Type wanted_argument ->
                 list_class_pairs state (argument, wanted_argument)
             | _ -> [])
           arguments wanted_arguments)
  | _ -> []

let explain_decision (site : State.decision_site) ~name ~decided =
  let took where = Printf.sprintf "%s took its default type, `%s`, %s." name decided where in
  let needs user =
    Printf.sprintf "%s needs the type of %s, so %s takes its default type `%s` here." user name name
      decided
  in
  match site with
  | Use ->
      ( Printf.sprintf "An earlier statement decided that the type of %s is `%s`." name decided,
        Printf.sprintf "This statement decides that the type of %s is `%s`." name decided )
  | Statement_end -> (took "at an earlier statement", needs "This statement")
  | Actual_head ->
      ( took "where the type of an earlier value was needed",
        Printf.sprintf "The type of this value is needed here, so %s takes its default type `%s`."
          name decided )
  | Method_call -> (took "at an earlier method call", needs "Method lookup")

let make_declaration_remedy name = Printf.sprintf "Declare `%s` with a type." name

let show_declaration : Path.t -> string = function
  | Method { owner; name; _ } -> Path.show_name owner ^ "." ^ name
  | path -> Path.show_name path

let make_bracket_remedy declared_on (parameter : Types.generic) =
  Printf.sprintf "Give `%s` its %s in brackets." (show_declaration declared_on)
    (match parameter.kind with
    | Types.Type_generic _ -> "type arguments"
    | Value_generic -> "arguments")

let find_log_report (state : State.state) ~fixes code span message (root, wanted) =
  let entries =
    List.map (fun (logged : State.logged) -> logged.entry) (State.list_class_log state root)
  in
  let literals =
    List.filter_map (function State.Literal { literal; _ } -> Some literal | _ -> None) entries
  in
  let quote id = State.quote_span state (State.read_span state id) in
  let wanted_type = State.normalize state wanted in
  let wanted = State.zonk state wanted in
  match
    List.find_opt
      (function
        | State.Literal { allowed; _ } | State.Narrowing { allowed; _ } ->
            State.is_within state wanted Types.number_types
            && not (State.is_within state wanted allowed)
        | State.Decided { decided_type; _ } -> not (Types.equal decided_type wanted_type)
        | State.Local _ | State.Origin _ -> false)
      entries
  with
  | Some (State.Literal { allowed; _ })
    when State.is_within state wanted Types.float_types && not (State.is_float_domain allowed) ->
      let spell_as_float literal =
        match state.tables.elaborations.(literal) with
        | Some (Literal (Integer_value number)) ->
            Printf.sprintf "`%s` as `%s.0`" (quote literal) (Z.to_string number)
        | _ -> State.raise_bug "`%s` is no integer literal" (quote literal)
      in
      Some
        (State.add_diagnostic state Integer_for_float span
           (Printf.sprintf "An integer literal is never a float, and %s is expected here. Write %s."
              (State.describe state wanted)
              (String.concat " and " (List.map spell_as_float literals))))
  | Some (State.Literal { allowed; report_excluded; _ })
    when State.is_within state wanted
           (if State.is_float_domain allowed then Types.float_types
            else Integer :: Types.integer_types) ->
      Some (report_excluded wanted)
  | Some (State.Narrowing { report_excluded; _ }) -> Some (report_excluded wanted)
  | Some (State.Decided { site; decided_type; decided_at }) ->
      let local = List.find_map (function State.Local local -> Some local | _ -> None) entries in
      let name =
        match (local, literals) with
        | Some local, _ -> quote local
        | None, literal :: _ -> quote literal
        | None, [] -> State.raise_bug "a number class has no literal"
      in
      let explanation, note =
        explain_decision site ~name:(Printf.sprintf "`%s`" name) ~decided:(Types.show decided_type)
      in
      let remedy =
        match local with
        | Some local
          when site <> Use
               && State.is_within state wanted Types.number_types
               && Hashtbl.mem state.annotatable local ->
            [ make_declaration_remedy name ]
        | _ -> []
      in
      let report =
        State.add_diagnostic state code span
          ~notes:[ (decided_at, note) ]
          ~fixes:(match site with Use -> fixes | Statement_end | Actual_head | Method_call -> [])
          (String.concat " " (message :: explanation :: remedy))
      in
      Unify.poison state.unifier root report;
      Some report
  | Some (State.Literal _ | State.Local _ | State.Origin _) | None -> None

let add_mismatch_diagnostic (state : State.state) ?(fixes = []) code
    (span : Source.Definition_span.t) ~(sides : (Types.ty * Types.ty) list) message =
  match find_refused_class state ~sides with
  | Some root -> report_decided_in_specification state span root
  | None -> (
      match
        List.find_map
          (find_log_report state ~fixes code span message)
          (List.concat_map (list_class_pairs state) sides)
      with
      | Some report -> report
      | None -> State.add_diagnostic state ~fixes code span message)

let add_mismatch ?fixes (state : State.state) (span : Source.Definition_span.t) ~expected ~actual =
  add_mismatch_diagnostic state ?fixes Mismatch span
    ~sides:[ (actual, expected); (expected, actual) ]
    (Printf.sprintf "Expected %s, found %s." (State.describe state expected)
       (State.describe state actual))

let add_operand_mismatch (state : State.state) ~(at : Source.Definition_span.t)
    ~left:((left_span : Source.Definition_span.t), left)
    ~right:((right_span : Source.Definition_span.t), right) =
  let left_type = State.normalize state left and right_type = State.normalize state right in
  if
    State.is_within state left_type Types.integer_types
    && State.is_within state right_type Types.integer_types
  then begin
    let is_range_within narrower wider =
      match (Types.find_integer_range narrower, Types.find_integer_range wider) with
      | Some (low, high), Some (wider_low, wider_high) ->
          Z.geq low wider_low && Z.leq high wider_high
      | _ -> false
    in
    let make_widening_fix side (operand : Source.Definition_span.t) target =
      State.fix
        (Printf.sprintf "Convert the %s side to `%s`." side (Types.show target))
        [
          State.replace operand
            (Printf.sprintf "%s.from_integer(%s)" (Types.show target)
               (State.quote_span state operand));
        ]
    in
    let fixes =
      if is_range_within right_type left_type then
        [ make_widening_fix "right" right_span left_type ]
      else if is_range_within left_type right_type then
        [ make_widening_fix "left" left_span right_type ]
      else []
    in
    add_mismatch_diagnostic state Mismatched_integers at
      ~sides:[ (left, right); (right, left) ]
      ~fixes
      (Printf.sprintf
         "Integer types never convert implicitly: this compares or combines `%s` with `%s`."
         (Types.show left_type) (Types.show right_type))
  end
  else add_mismatch state right_span ~expected:left ~actual:right

let report_mismatch ?fixes (state : State.state) span ~expected ~actual =
  ignore (add_mismatch ?fixes state span ~expected ~actual)

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
        add_mismatch_diagnostic state Unsatisfied_bound at ~sides
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
      add_operand_mismatch state ~at ~left:(left, goal.subject) ~right:(right, argument)
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
  | (Method_call at | Loop at | Quantifier at), Implements trait ->
      State.add_diagnostic state
        (match goal.cause with Loop _ | Quantifier _ -> Not_iterable | _ -> No_impl)
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
  | (Bound _ | Operator _ | Method_call _ | Loop _ | Quantifier _ | Any_conversion _), Within _ ->
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

let holds_class (state : State.state) root type_ =
  List.exists
    (function Unify.Unknown_type index | Unknown_value index -> index = root)
    (Unify.list_unknowns state.unifier type_)

let find_refused_class (state : State.state) ~sides =
  Option.bind state.unifier.refused_code_unknown (fun root ->
      if List.exists (fun (side, _) -> holds_class state root side) sides then Some root else None)

let report_decided_in_specification (state : State.state) at root =
  let local =
    Array.find_index
      (Option.fold ~none:false ~some:(holds_class state root))
      state.tables.local_types
  in
  let report =
    State.add_diagnostic state
      (Decided_in_specification { at; local = Option.map (fun local -> Core.Written local) local })
  in
  Unify.poison state.unifier (Unknown_type root) report;
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

let find_log_report (state : State.state) at mismatch (root, wanted) =
  let entries =
    List.map (fun (logged : State.logged) -> logged.entry) (State.list_class_log state root)
  in
  let literals =
    List.filter_map (function State.Literal { literal; _ } -> Some literal | _ -> None) entries
  in
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
      let read_number literal =
        match state.tables.elaborations.(literal) with
        | Some (Literal (Integer_value number)) -> (Core.Written literal, number)
        | _ -> State.raise_bug "a number class holds a literal that is not an integer"
      in
      Some
        (State.add_diagnostic state
           (Integer_for_float
              {
                at;
                wanted = State.make_shown state wanted;
                literals = List.map read_number literals;
              }))
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
        | Some local, _ -> local
        | None, literal :: _ -> literal
        | None, [] -> State.raise_bug "a number class has no literal"
      in
      let declares =
        match local with
        | Some local ->
            site <> Use
            && State.is_within state wanted Types.number_types
            && Hashtbl.mem state.annotatable local
        | None -> false
      in
      let report =
        State.add_diagnostic state
          (Mismatch
             {
               at;
               mismatch;
               decision =
                 Some { name = Written name; decided = decided_type; site; decided_at; declares };
             })
      in
      Unify.poison state.unifier (Unknown_type root) report;
      Some report
  | Some (State.Literal _ | State.Local _ | State.Origin _) | None -> None

let add_mismatch_diagnostic (state : State.state) at ~(sides : (Types.ty * Types.ty) list) mismatch
    =
  match find_refused_class state ~sides with
  | Some root -> report_decided_in_specification state at root
  | None -> (
      match
        List.find_map
          (find_log_report state at mismatch)
          (List.concat_map (list_class_pairs state) sides)
      with
      | Some report -> report
      | None -> State.add_diagnostic state (Mismatch { at; mismatch; decision = None }))

let add_mismatch ?copy (state : State.state) at ~expected ~actual =
  add_mismatch_diagnostic state at
    ~sides:[ (actual, expected); (expected, actual) ]
    (Expected
       { expected = State.make_shown state expected; actual = State.make_shown state actual; copy })

let add_operand_mismatch (state : State.state) ~at ~left:(left_origin, left)
    ~right:(right_origin, right) =
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
    let widening : Catalog.Inference.widening option =
      if is_range_within right_type left_type then
        Some { side = Right; operand = right_origin; target = left_type }
      else if is_range_within left_type right_type then
        Some { side = Left; operand = left_origin; target = right_type }
      else None
    in
    add_mismatch_diagnostic state at
      ~sides:[ (left, right); (right, left) ]
      (Mismatched_integers { left = left_type; right = right_type; widening })
  end
  else add_mismatch state right_origin ~expected:left ~actual:right

let report_mismatch ?copy (state : State.state) at ~expected ~actual =
  ignore (add_mismatch ?copy state at ~expected ~actual)

let report_unmet_bound (state : State.state) ~at ~of_type ~sides ~impl_need subject
    (bound : Types.trait_reference) ~associated =
  let frame = State.read_current_frame state in
  match
    List.find_opt
      (fun (reported, reported_bound, _) -> Types.equal reported subject && reported_bound = bound)
      frame.reported_unmet_bounds
  with
  | Some (_, _, report) -> report
  | None ->
      let unmet : Catalog.Inference.unmet_bound =
        match associated with
        | None when Types.is_view subject -> Does_not_hold_for_view
        | None -> Does_not_hold
        | Some (name, found, _) -> Associated_differs { name; found = State.zonk state found }
      in
      let report =
        add_mismatch_diagnostic state at ~sides
          (Unsatisfied_bound
             { of_type = Option.map (State.zonk state) of_type; subject; bound; unmet; impl_need })
      in
      frame.reported_unmet_bounds <- (subject, bound, report) :: frame.reported_unmet_bounds;
      report

let report_requirement (state : State.state) (goal : State.goal) ?associated ~impl_need subject =
  let shown = State.normalize state subject in
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
      report_unmet_bound state ~at ~of_type ~sides ~impl_need shown bound ~associated
  | ( Operator { at; operands = Some (left, right) },
      Implements { trait_arguments = [ Types.Type argument ]; _ } )
    when Option.is_none associated && Option.is_none impl_need
         && State.is_within state goal.subject Types.number_types
         && State.is_within state argument Types.number_types ->
      add_operand_mismatch state ~at ~left:(left, goal.subject) ~right:(right, argument)
  | Operator { at; _ }, Implements trait ->
      State.add_diagnostic state
        (match associated with
        | Some (_, found, wanted) ->
            Operator_output
              { at; found = State.zonk state found; wanted = State.zonk state wanted; impl_need }
        | None ->
            Operator_not_implemented
              { at; subject = shown; trait = Unify.zonk_trait state.unifier trait; impl_need })
  | (Method_call at | Loop at | Quantifier at), Implements trait ->
      State.add_diagnostic state
        (Not_implemented
           {
             at;
             subject = shown;
             trait = Unify.zonk_trait state.unifier trait;
             is_iteration = (match goal.cause with Loop _ | Quantifier _ -> true | _ -> false);
             impl_need;
           })
  | (Bound _ | Operator _ | Method_call _ | Loop _ | Quantifier _), Within _ ->
      State.raise_bug "a goal's cause does not fit its requirement"

let report_failure (state : State.state) (goal : State.goal) ?associated subject =
  match (goal.needed_by, goal.requirement) with
  | None, _ -> report_requirement state goal ?associated ~impl_need:None subject
  | Some root, Implements condition ->
      report_requirement state root root.subject
        ~impl_need:
          (Some
             {
               needing = State.zonk state subject;
               condition = Unify.zonk_trait state.unifier condition;
             })
  | Some _, Within _ -> State.raise_bug "an impl's condition is a set of types"

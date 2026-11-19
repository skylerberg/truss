let list_argument_types (trait : Types.trait_reference) =
  List.filter_map
    (function Types.Type type_ -> Some type_ | Types.Value _ -> None)
    trait.trait_arguments

let is_absorbing : Types.ty -> bool = function Error _ | Hole -> true | _ -> false

let find_absorbing (state : State.state) types =
  List.find_map
    (fun type_ ->
      let absorbing = ref None in
      ignore
        (Types.exists ~resolve:(State.resolve state)
           (fun part ->
             if is_absorbing part && Option.is_none !absorbing then absorbing := Some part;
             is_absorbing part)
           type_);
      !absorbing)
    types

let list_obligation_unknowns (state : State.state) (obligation : State.obligation) =
  Unify.list_unknowns state.unifier (State.normalize state obligation.subject)
  @
  match obligation.requirement with
  | Implements { trait; _ } ->
      List.concat_map
        (Unify.list_argument_unknowns state.unifier)
        (Unify.zonk_trait state.unifier trait).trait_arguments
  | Within _ | When_solved _ -> []

type outcome = Pending | Met | Unmet of Diagnostic.reported | Vacuous

let list_covering_traits (state : State.state) root =
  let domain = Unify.read_domain state.unifier root in
  List.filter_map
    (fun sealed ->
      let path = Well_known.make_path sealed in
      match Scalar_set.find_sealed_implementors path with
      | Some implementors when Scalar_set.is_subset domain ~of_:implementors ->
          Some (State.make_trait_reference ~arguments:[] path)
      | _ -> None)
    [ Fixed_width_integer; Signed_integer; Unsigned_integer; Floating_point ]

let solve_number_associated_types (state : State.state) root (trait : Types.trait_reference) =
  let subject = Types.Number_variable root in
  let bounds =
    List.concat_map
      (fun covering ->
        covering
        :: Interface.Properties.list_bound_closure state.lookups.interface ~self:subject covering)
      (list_covering_traits state root)
  in
  let arguments = (Unify.zonk_trait state.unifier trait).trait_arguments in
  List.iter
    (fun (name, wanted) ->
      match
        List.find_map
          (fun (bound : Types.trait_reference) ->
            if
              Path.equal bound.trait trait.trait
              && (Unify.zonk_trait state.unifier bound).trait_arguments = arguments
            then List.assoc_opt name bound.associated
            else None)
          bounds
      with
      | Some fixed -> ignore (State.unify state wanted fixed)
      | None -> ())
    trait.associated

let report_within (state : State.state) reason (span : Source.Definition_span.t) ~members ~found =
  let notes =
    match State.resolve state found with
    | Types.Number_variable root -> (
        match
          List.find_opt
            (fun (narrowing : State.narrowing) ->
              State.resolve state (Types.Number_variable narrowing.variable)
              = Types.Number_variable root
              && Scalar_set.is_empty (Scalar_set.inter narrowing.members members))
            state.narrowings
        with
        | Some narrowing ->
            [
              ( narrowing.narrowed_at,
                Printf.sprintf "Here it becomes %s." (Scalar_set.describe narrowing.members) );
            ]
        | None -> [])
    | _ -> []
  in
  match State.explain_narrowing state reason ~found with
  | Some (code, message) -> State.add_diagnostic state ~notes code span message
  | None ->
      State.add_diagnostic state ~notes Mismatch span
        (Printf.sprintf "Expected %s, found %s." (Scalar_set.describe members)
           (State.describe state found))

let rec decide (state : State.state) (obligation : State.obligation) =
  let subject = State.normalize state obligation.subject in
  match obligation.requirement with
  | Implements implements -> (
      let trait =
        State.normalize_trait state (State.solve_trait_arguments state subject implements.trait)
      in
      let unannotated = { trait with associated = [] } in
      match (State.resolve state subject, Scalar_set.find_sealed_implementors trait.trait) with
      | Types.Number_variable root, Some implementors
        when not (Scalar_set.is_subset (Unify.read_domain state.unifier root) ~of_:implementors) ->
          if Unify.narrow state.unifier root implementors then begin
            State.record_narrowing state ~variable:root ~span:implements.span ~members:implementors
              (Sealed_bound trait.trait);
            decide state obligation
          end
          else Unmet (implements.on_unmet subject None)
      | resolved, _ -> (
          (match resolved with
          | Types.Number_variable root -> solve_number_associated_types state root trait
          | _ -> ());
          if list_obligation_unknowns state obligation <> [] then Pending
          else
            match find_absorbing state (subject :: list_argument_types trait) with
            | Some absorbing ->
                List.iter
                  (fun (_, wanted) -> ignore (State.unify state wanted absorbing))
                  trait.associated;
                Vacuous
            | None -> (
                match State.find_evidence state subject unannotated with
                | None ->
                    let report = implements.on_unmet subject None in
                    state.unmet_impls <- (subject, unannotated, report) :: state.unmet_impls;
                    List.iter
                      (fun (_, wanted) -> ignore (State.unify state wanted (Types.Error report)))
                      trait.associated;
                    Unmet report
                | Some evidence ->
                    List.iter
                      (fun (name, wanted) ->
                        match
                          Interface.Impls.project_associated_type state.lookups.interface
                            ~list_bounds:(State.lookup_bounds state) subject unannotated name
                        with
                        | Some actual when not (State.unify state actual wanted) ->
                            ignore (implements.on_unmet subject (Some (name, actual)))
                        | _ -> ())
                      trait.associated;
                    implements.on_met evidence;
                    Met)))
  | Within within -> (
      match State.resolve state subject with
      | Types.Error _ | Types.Hole -> Vacuous
      | Types.Variable _ -> Pending
      | Types.Number_variable root ->
          if Scalar_set.is_subset (Unify.read_domain state.unifier root) ~of_:within.members then
            Pending
          else if Unify.narrow state.unifier root within.members then begin
            State.record_narrowing state ~variable:root ~span:within.span ~members:within.members
              within.reason;
            decide state obligation
          end
          else
            Unmet
              (report_within state within.reason within.span ~members:within.members ~found:subject)
      | resolved ->
          if State.is_within state within.members resolved then begin
            within.on_met resolved;
            Met
          end
          else
            Unmet
              (report_within state within.reason within.span ~members:within.members ~found:resolved)
      )
  | When_solved check -> (
      if Unify.list_unknowns state.unifier subject <> [] then Pending
      else
        match find_absorbing state [ subject ] with
        | Some _ -> Vacuous
        | None ->
            check subject;
            Met)

let is_pending state obligation =
  match decide state obligation with Pending -> true | Met | Unmet _ | Vacuous -> false

let add (state : State.state) (obligation : State.obligation) =
  (match obligation.requirement with
  | Implements { trait; _ } ->
      Option.iter
        (fun level ->
          List.iter (fun (_, wanted) -> Unify.lower state.unifier ~level wanted) trait.associated)
        (Unify.find_lowest_level state.unifier (list_obligation_unknowns state obligation))
  | Within _ | When_solved _ -> ());
  let outcome = decide state obligation in
  (match (outcome, State.find_current_frame state) with
  | Pending, Some frame -> frame.obligations <- obligation :: frame.obligations
  | Pending, None ->
      State.raise_bug "an obligation on `%s` outside every statement is not decided"
        (State.show state obligation.subject)
  | (Met | Unmet _ | Vacuous), _ -> ());
  outcome

let require state subject trait ~span ~on_met ~on_unmet =
  ignore (add state { subject; requirement = Implements { trait; span; on_met; on_unmet } })

let describe_associated_type (state : State.state) base (trait : Types.trait_reference) name =
  Printf.sprintf "the `%s` of `%s` under `%s`" name (State.show state base)
    (Types.show_trait { (Unify.zonk_trait state.unifier trait) with associated = [] })

let describe_compared_type (state : State.state) : Types.ty -> string = function
  | Projection { base; trait; name } -> describe_associated_type state base trait name
  | type_ -> Printf.sprintf "`%s`" (State.show state type_)

let describe_projection_mismatch (state : State.state) base trait name ~actual ~wanted =
  let associated_type = describe_associated_type state base trait name in
  if
    Types.equal (State.zonk state actual)
      (State.zonk state (Types.Projection { base; trait = { trait with associated = [] }; name }))
  then
    Printf.sprintf "%s may differ from %s."
      (String.capitalize_ascii associated_type)
      (describe_compared_type state wanted)
  else
    Printf.sprintf "%s is %s, and %s is expected."
      (String.capitalize_ascii associated_type)
      (describe_compared_type state actual)
      (describe_compared_type state wanted)

let require_projection_equalities (state : State.state) (frame : State.frame) =
  let equalities = List.rev state.unifier.deferred_projection_equalities in
  state.unifier.deferred_projection_equalities <- [];
  List.iter
    (function
      | Types.Projection { base; trait; name }, wanted ->
          require state base
            { trait with associated = [ (name, wanted) ] }
            ~span:frame.span ~on_met:ignore
            ~on_unmet:(fun base mismatch ->
              match mismatch with
              | Some (_, actual) ->
                  State.add_diagnostic state Mismatch frame.span
                    (describe_projection_mismatch state base trait name ~actual ~wanted)
              | None -> (
                  match State.find_unmet_impl state base (State.normalize_trait state trait) with
                  | Some report -> report
                  | None ->
                      State.add_diagnostic state No_impl frame.span
                        (Printf.sprintf "`%s` does not implement `%s`, so it has no `%s`."
                           (Types.show base)
                           (Types.show_trait (Unify.zonk_trait state.unifier trait))
                           name)))
      | projection, _ ->
          State.raise_bug "`%s` is deferred, and it is not an associated type"
            (State.show state projection))
    equalities

let rec solve (state : State.state) (frame : State.frame) =
  let pending = List.rev frame.obligations in
  frame.obligations <- [];
  let remaining = List.filter (is_pending state) pending in
  frame.obligations <- frame.obligations @ List.rev remaining;
  let has_deferred = state.unifier.deferred_projection_equalities <> [] in
  require_projection_equalities state frame;
  if List.length remaining < List.length pending || has_deferred then solve state frame

let require_within state subject ~members ~reason ~span ?(on_met = ignore) () =
  match add state { subject; requirement = Within { members; reason; span; on_met } } with
  | Unmet report -> Types.Error report
  | Pending | Met | Vacuous -> subject

let check_solved state type_ check =
  ignore (add state { subject = type_; requirement = When_solved check })

let choose_default (state : State.state) root =
  let domain = Unify.read_domain state.unifier root in
  match Scalar_set.choose_default domain with
  | Some member -> Scalar_set.make_type member
  | None -> State.raise_bug "%s has no default type" (Scalar_set.describe domain)

let make_undecided_type (undecided : State.undecided_literal) =
  Types.Number_variable undecided.index

let record_decisions (state : State.state) ~(at : Source.Definition_span.t) ~is_default =
  state.undecided <-
    List.filter
      (fun (undecided : State.undecided_literal) ->
        match Unify.resolve state.unifier (make_undecided_type undecided) with
        | Types.Number_variable _ -> true
        | _ ->
            Hashtbl.replace state.decisions undecided.index
              {
                decided_local = undecided.local;
                decided_type = Unify.zonk state.unifier (make_undecided_type undecided);
                decided_at = at;
                is_default;
                decision_report = None;
              };
            false)
      state.undecided

let decide_for_method_call (state : State.state) ~at type_ =
  match
    ( List.filter_map
        (function Unify.Unknown_number root -> Some root | _ -> None)
        (Unify.list_unknowns state.unifier (State.normalize state type_)),
      State.find_current_frame state )
  with
  | [], _ -> type_
  | literals, Some frame ->
      List.iter (solve state) state.frames;
      record_decisions state ~at:frame.span ~is_default:false;
      List.iter
        (fun root ->
          match Unify.resolve state.unifier (Types.Number_variable root) with
          | Types.Number_variable root ->
              ignore (State.unify state (Types.Number_variable root) (choose_default state root));
              List.iter (solve state) state.frames
          | _ -> ())
        literals;
      record_decisions state ~at ~is_default:true;
      State.normalize state type_
  | _ :: _, None -> State.raise_bug "a method is called outside every statement"

let constrain_capability_equalities (state : State.state) (frame : State.frame) =
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
  state.unifier.deferred_capability_equalities <- []

let list_frame_unknowns (state : State.state) (frame : State.frame) =
  let list_types ids table = List.filter_map (fun id -> table.(id)) ids in
  let call_arguments =
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
  List.concat_map
    (Unify.list_unknowns state.unifier)
    (list_types frame.recorded_expressions state.tables.types
    @ list_types frame.bindings state.tables.local_types)
  @ List.concat_map (Unify.list_argument_unknowns state.unifier) call_arguments

let is_owned_by (state : State.state) (frame : State.frame) unknown =
  Unify.read_level state.unifier (Unify.read_unknown_index unknown) >= frame.level

let hand_literals_to_parent (state : State.state) (frame : State.frame) ~escaping
    (parent : State.frame) =
  let declared =
    List.filter_map
      (fun local -> Option.map (fun type_ -> (local, type_)) state.tables.local_types.(local))
      frame.declared
  in
  if parent.frame_specification = frame.frame_specification then
    List.iter
      (fun (local, type_) ->
        List.iter
          (function
            | Unify.Unknown_number index as unknown when is_owned_by state frame unknown ->
                Unify.lower_to state.unifier ~level:parent.level index;
                state.undecided <- { index; local } :: state.undecided
            | _ -> ())
          (Unify.list_reachable_unknowns state.unifier (State.normalize state type_)))
      (declared @ escaping)

let default_literals (state : State.state) (frame : State.frame) =
  let literals =
    List.sort_uniq compare
      (List.filter_map
         (function
           | Unify.Unknown_number index as unknown when is_owned_by state frame unknown ->
               Some index
           | _ -> None)
         (list_frame_unknowns state frame))
  in
  List.iter
    (fun index ->
      match Unify.resolve state.unifier (Types.Number_variable index) with
      | Types.Number_variable root ->
          Hashtbl.replace state.unifier.type_solutions root (choose_default state root);
          solve state frame
      | _ -> ())
    literals

let report_unsolved (state : State.state) (frame : State.frame) unsolved =
  let list_trait_unknowns (trait : Types.trait_reference) =
    List.concat_map (Unify.list_argument_unknowns state.unifier) trait.trait_arguments
  in
  let find_undetermined_trait : Tables.callee -> Types.trait_reference option = function
    | Trait_method { trait; self_type; _ }
      when (not (Types.contains_unsolved (State.zonk state self_type)))
           && List.exists (fun unknown -> List.mem unknown unsolved) (list_trait_unknowns trait) ->
        Some trait
    | _ -> None
  in
  let list_loop_calls : Tables.loop -> Tables.call list = function
    | Elements { count; element; _ } -> [ count; element ]
    | Pulled { cursor_call; remaining; _ } -> List.filter_map Fun.id [ cursor_call; remaining ]
    | Integer_range _ -> []
  in
  let undetermined =
    List.filter_map
      (fun id ->
        Option.bind state.tables.calls.(id) (fun (call : Tables.call) ->
            Option.map
              (fun trait ->
                ( id,
                  trait,
                  Printf.sprintf
                    "This call does not determine the arguments of `%s`. Write the call in full \
                     with them." ))
              (find_undetermined_trait call.callee)))
      frame.recorded_expressions
    @ List.filter_map
        (fun (loop, iterable) ->
          Option.bind state.tables.loops.(loop) (fun record ->
              Option.map
                (fun trait ->
                  ( iterable,
                    trait,
                    Printf.sprintf
                      "This loop does not determine the arguments of `%s`, whose methods give its \
                       elements." ))
                (List.find_map
                   (fun (call : Tables.call) -> find_undetermined_trait call.callee)
                   (list_loop_calls record))))
        frame.recorded_loops
  in
  let trait_reports =
    List.map
      (fun (id, (trait : Types.trait_reference), describe) ->
        State.add_diagnostic state Cannot_infer (State.read_span state id)
          (describe (match trait.trait with Top { name; _ } -> name | path -> Path.show path)))
      undetermined
  in
  let explained = List.concat_map (fun (_, trait, _) -> list_trait_unknowns trait) undetermined in
  let report =
    match trait_reports with
    | first :: _ when List.for_all (fun unknown -> List.mem unknown explained) unsolved -> first
    | _ ->
        State.add_diagnostic state Cannot_infer frame.span
          "The types in this statement cannot be inferred from it alone. Give the `let` a type, or \
           the call type arguments, such as `var names: List[String] = []`."
  in
  if Option.is_none state.unsolved then state.unsolved <- Some report;
  List.iter
    (function
      | Unify.Unknown_type index | Unknown_number index ->
          Hashtbl.replace state.unifier.type_solutions index (Types.Error report)
      | Unknown_value _ -> ())
    unsolved

let finish_tables (state : State.state) (frame : State.frame) ~parent ~is_open =
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
    (List.sort (State.compare_in_source_order state) settled_expressions)

let settle (state : State.state) (frame : State.frame) ~escaping =
  constrain_capability_equalities state frame;
  solve state frame;
  let parent = match state.frames with _ :: parent :: _ -> Some parent | _ -> None in
  record_decisions state ~at:frame.span ~is_default:false;
  Option.iter (hand_literals_to_parent state frame ~escaping) parent;
  state.undecided <-
    List.filter
      (fun (undecided : State.undecided_literal) ->
        match Unify.resolve state.unifier (make_undecided_type undecided) with
        | Types.Number_variable root -> not (is_owned_by state frame (Unknown_number root))
        | _ -> true)
      state.undecided;
  default_literals state frame;
  let unsolved =
    List.sort_uniq compare (List.filter (is_owned_by state frame) (list_frame_unknowns state frame))
  in
  if unsolved <> [] then begin
    report_unsolved state frame unsolved;
    solve state frame
  end;
  let is_open unknown = not (is_owned_by state frame unknown) in
  finish_tables state frame ~parent ~is_open;
  match parent with
  | Some parent ->
      parent.obligations <-
        List.filter
          (fun obligation -> List.for_all is_open (list_obligation_unknowns state obligation))
          frame.obligations
        @ parent.obligations
  | None -> ()

let run_frame (state : State.state) (env : State.env) (span : Source.Definition_span.t) body
    ~list_escaping =
  state.unifier.level <- state.unifier.level + 1;
  let frame : State.frame =
    {
      level = state.unifier.level;
      recorded_expressions = [];
      recorded_loops = [];
      bindings = [];
      declared = [];
      obligations = [];
      reported_unmet_bounds = [];
      compiled_expressions = [];
      compiled_bindings = [];
      specification_only_report = None;
      frame_specification = env.specification;
      span;
    }
  in
  state.frames <- frame :: state.frames;
  let result = body () in
  settle state frame ~escaping:(list_escaping result);
  state.frames <- List.tl state.frames;
  state.unifier.level <- state.unifier.level - 1;
  (match (state.frames, state.unifier.deferred_projection_equalities) with
  | [], (projection, _) :: _ ->
      State.raise_bug "the equality of `%s` is not decided after every statement"
        (State.show state projection)
  | _ -> ());
  result

let run_in_statement state env span body =
  run_frame state env span body ~list_escaping:(fun () -> [])

let infer_in_statement state env (value : Syntax.expression) =
  State.normalize state
    (run_frame state env (State.read_span state value.id)
       (fun () -> Hooks.check_expression state env value)
       ~list_escaping:(fun type_ -> [ (value.id, type_) ]))

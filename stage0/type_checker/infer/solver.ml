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
  | Satisfies _ -> []

type outcome = Pending | Met | Unmet of Diagnostic.reported | Vacuous

let decide (state : State.state) (obligation : State.obligation) =
  let subject = State.normalize state obligation.subject in
  match obligation.requirement with
  | Implements implements -> (
      let trait =
        State.normalize_trait state (State.solve_trait_arguments state subject implements.trait)
      in
      let unannotated = { trait with associated = [] } in
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
                Met))
  | Satisfies satisfies -> (
      if list_obligation_unknowns state obligation <> [] then Pending
      else
        match find_absorbing state [ subject ] with
        | Some _ -> Vacuous
        | None ->
            if satisfies.holds subject then begin
              satisfies.on_met subject;
              Met
            end
            else Unmet (satisfies.on_unmet subject))

let is_met_by_trial (state : State.state) (obligation : State.obligation) =
  let subject = State.normalize state obligation.subject in
  let is_open types =
    List.exists (fun type_ -> Unify.list_unknowns state.unifier type_ <> []) types
    || Option.is_some (find_absorbing state types)
  in
  match obligation.requirement with
  | Implements { trait; _ } -> (
      is_open [ subject ]
      ||
      match (Types.find_builtin subject, Types.find_integer_implementors trait.trait) with
      | Some builtin, Some implementors -> List.mem builtin implementors
      | _ -> true)
  | Satisfies { holds; _ } -> is_open [ subject ] || holds subject

let is_pending state obligation =
  match decide state obligation with Pending -> true | Met | Unmet _ | Vacuous -> false

let rec solve (state : State.state) (frame : State.frame) =
  let pending = List.rev frame.obligations in
  frame.obligations <- [];
  let remaining = List.filter (is_pending state) pending in
  frame.obligations <- frame.obligations @ List.rev remaining;
  if List.length remaining < List.length pending then solve state frame

let add (state : State.state) (obligation : State.obligation) =
  (match obligation.requirement with
  | Implements { trait; _ } ->
      Option.iter
        (fun level ->
          List.iter (fun (_, wanted) -> Unify.lower state.unifier ~level wanted) trait.associated)
        (Unify.find_lowest_level state.unifier (list_obligation_unknowns state obligation))
  | Satisfies _ -> ());
  let outcome = decide state obligation in
  (match (outcome, State.find_current_frame state) with
  | Pending, Some frame -> frame.obligations <- obligation :: frame.obligations
  | _ -> ());
  outcome

let require state subject trait ~on_met ~on_unmet =
  ignore (add state { subject; requirement = Implements { trait; on_met; on_unmet } })

let require_type state subject ~holds ?(on_met = ignore) ~on_unmet () =
  match add state { subject; requirement = Satisfies { holds; on_met; on_unmet } } with
  | Unmet report -> Types.Error report
  | Pending | Met | Vacuous -> subject

let check_solved state type_ check =
  ignore
    (require_type state type_
       ~holds:(fun _ -> true)
       ~on_met:check
       ~on_unmet:(fun _ -> State.raise_bug "a check that always holds is unmet")
       ())

let list_default_types ~specification (kind : Types.literal_kind) =
  match kind with
  | Integer_literal ->
      (if specification then [ Types.Integer ] else [])
      @ [ Types.make_builtin Int64; Types.make_builtin UInt64 ]
  | Float_literal -> [ Types.make_builtin Float64 ]

let choose_default (state : State.state) ~specification ~obligations (kind, root) =
  let specification = specification && not (Hashtbl.mem state.unifier.code_literals root) in
  let is_met_by default =
    Hashtbl.replace state.unifier.type_solutions root default;
    let is_met = List.for_all (is_met_by_trial state) obligations in
    Hashtbl.remove state.unifier.type_solutions root;
    is_met
  in
  match list_default_types ~specification kind with
  | [] -> State.raise_bug "a literal kind has no default type"
  | first :: _ as defaults -> (
      match List.find_opt is_met_by defaults with Some default -> default | None -> first)

let make_undecided_type (undecided : State.undecided_literal) =
  Types.Literal (undecided.kind, undecided.index)

let record_decisions (state : State.state) ~(at : Source.Definition_span.t) ~is_default =
  state.undecided <-
    List.filter
      (fun (undecided : State.undecided_literal) ->
        match Unify.resolve state.unifier (make_undecided_type undecided) with
        | Types.Literal _ -> true
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
  match (State.resolve state type_, State.find_current_frame state) with
  | Types.Literal (kind, root), Some frame ->
      List.iter (solve state) state.frames;
      record_decisions state ~at:frame.span ~is_default:false;
      let default =
        choose_default state ~specification:false
          ~obligations:
            (List.concat_map (fun (frame : State.frame) -> frame.obligations) state.frames)
          (kind, root)
      in
      ignore (State.unify state type_ default);
      record_decisions state ~at ~is_default:true;
      default
  | Types.Literal _, None -> State.raise_bug "a method is called outside every statement"
  | _ -> type_

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
            | Unify.Unknown_literal (kind, index) as unknown when is_owned_by state frame unknown ->
                Unify.lower_to state.unifier ~level:parent.level index;
                if not frame.frame_specification then
                  Hashtbl.replace state.unifier.code_literals index ();
                state.undecided <- { index; kind; local } :: state.undecided
            | _ -> ())
          (Unify.list_unknowns state.unifier type_))
      (declared @ escaping)

let default_literals (state : State.state) (frame : State.frame) =
  let literals =
    List.sort_uniq compare
      (List.filter_map
         (function
           | Unify.Unknown_literal (kind, index) as unknown when is_owned_by state frame unknown ->
               Some (index, kind)
           | _ -> None)
         (list_frame_unknowns state frame))
  in
  List.iter
    (fun (index, kind) ->
      match Unify.resolve state.unifier (Types.Literal (kind, index)) with
      | Types.Literal (kind, root) ->
          let default =
            choose_default state ~specification:frame.frame_specification
              ~obligations:frame.obligations (kind, root)
          in
          Hashtbl.replace state.unifier.type_solutions root default;
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
      | Unify.Unknown_type index | Unknown_literal (_, index) ->
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
        | Types.Literal (kind, root) -> not (is_owned_by state frame (Unknown_literal (kind, root)))
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
  result

let run_in_statement state env span body =
  run_frame state env span body ~list_escaping:(fun () -> [])

let infer_in_statement state env (value : Syntax.expression) =
  run_frame state env (State.read_span state value.id)
    (fun () -> Hooks.check_expression state env value)
    ~list_escaping:(fun type_ -> [ (value.id, type_) ])

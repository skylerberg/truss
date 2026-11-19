type conversion =
  | From_never
  | Owned_to_view
  | View_to_owned
  | Function_widening
  | To_integer
  | From_integer

let read_head (state : State.state) ?default_at type_ =
  match State.normalize state type_ with
  | Types.Variable root ->
      Solver.solve_head state ?default_at root;
      State.normalize state type_
  | head -> head

let read_expected_head state type_ = read_head state type_

let read_actual_head state (value : Syntax.expression) type_ =
  read_head state ~default_at:(State.read_span state value.id) type_

let read_checked_head state env (value : Syntax.expression) =
  read_actual_head state value (Hooks.check_expression state env value)

let find_view_as ~owned ~view =
  match (Types.find_view owned, view) with
  | Some (Types.Named { path; _ } as owned_view), Types.Named { path = view_path; _ }
    when Path.equal path view_path ->
      Some owned_view
  | _ -> None

let convert (state : State.state) (env : State.env) ?argument ?(takes_view_as_owner = false)
    ?expression (span : Source.Definition_span.t) ~actual ~expected =
  let is_argument = Option.is_some argument in
  let record_conversion (conversion : conversion option) =
    match (conversion, expression) with
    | Some conversion, Some id ->
        let before = state.form.expression_builders.(id) in
        state.form.expression_builders.(id) <-
          Option.map
            (fun build () ->
              let inner : Core.expression = build () in
              let expected = State.finalize_type state expected in
              let convert conversion =
                State.make_synthetic_expression state ~origin:id expected
                  (Convert { conversion; value = inner })
              in
              match conversion with
              | From_never -> inner
              | Function_widening ->
                  if Types.equal inner.type_ expected then inner else convert Widen
              | To_integer -> convert To_integer
              | From_integer -> convert From_integer
              | View_to_owned -> convert View_to_owned
              | Owned_to_view
                when Types.is_well_known List inner.type_ || Types.is_builtin Array inner.type_ ->
                  let base : Core.place =
                    match inner.kind with Use place -> place | _ -> Temporary inner
                  in
                  State.make_synthetic_expression state ~origin:id expected
                    (State.make_range state ~origin:id base ~start:None ~stop:None ~inclusive:false)
              | Owned_to_view -> (
                  match inner.type_ with
                  | Types.Named { path; arguments } ->
                      State.make_synthetic_expression state ~origin:id expected
                        (Call
                           (State.make_call state
                              ~callee:
                                (Function
                                   {
                                     path =
                                       Method
                                         { owner = path; name = "slice"; receiver = Instance Read };
                                     instantiation =
                                       { Types.no_instantiation with type_arguments = arguments };
                                   })
                              ~arguments:[ Operands.build_argument Read inner ]
                              ~lends:None))
                  | other -> State.raise_bug "`%s` is viewed and has no view" (Types.show other)))
            before
    | _ -> ()
  in
  record_conversion
  @@
  let actual_type = read_head state ~default_at:span actual in
  let wanted = read_expected_head state expected in
  let refuse () =
    State.report_mismatch state span ~expected ~actual;
    None
  in
  let between_owner_and_view =
    match if is_argument then find_view_as ~owned:actual_type ~view:wanted else None with
    | Some view -> Some (Owned_to_view, wanted, view)
    | None when takes_view_as_owner -> (
        match wanted with
        | Types.Named { path; _ } when Well_known.is List path || Well_known.is String path ->
            Option.map
              (fun view -> (View_to_owned, actual_type, view))
              (find_view_as ~owned:wanted ~view:actual_type)
        | _ -> None)
    | None -> None
  in
  match between_owner_and_view with
  | Some (conversion, written_view, view) ->
      if not (Unify.unify state.unifier written_view view) then
        State.report_mismatch state span ~expected ~actual;
      Some conversion
  | None -> (
      match (actual_type, wanted, expression) with
      | Types.Never, _, _ -> Some From_never
      | Types.Integer, _, Some _
        when is_argument && env.specification && State.is_within state wanted Types.integer_types ->
          Some From_integer
      | _, Types.Integer, _
        when env.specification && State.is_within state actual_type Types.integer_types ->
          Some To_integer
      | Types.Function actual_function, Types.Function wanted_function, _
        when not (Types.has_same_clauses actual_function wanted_function) ->
          let unlisted =
            Types.compute_missing_capabilities
              ~implies:
                (Interface.Impls.implies_condition state.lookups.interface
                   ~list_bounds:(State.lookup_bounds state))
              ~required:actual_function.uses ~available:wanted_function.uses
          in
          let unknown =
            Types.has_unsolved_capabilities actual_function.uses
            || Types.has_unsolved_capabilities wanted_function.uses
          in
          let proven =
            Types.costs_imply ~provided:actual_function.costs ~required:wanted_function.costs
          in
          if
            Unify.unify state.unifier wanted
              (Types.Function
                 { actual_function with uses = wanted_function.uses; costs = wanted_function.costs })
            && (unlisted = Types.no_capabilities || unknown)
            && proven
          then begin
            if unlisted <> Types.no_capabilities then
              state.capability_constraints <-
                {
                  subset = actual_function.uses;
                  restriction = None;
                  superset = wanted_function.uses;
                  report_missing =
                    (fun _ ->
                      State.report_mismatch state span
                        ~expected:(State.finalize_type state expected)
                        ~actual:(State.finalize_type state actual));
                }
                :: state.capability_constraints;
            Some Function_widening
          end
          else refuse ()
      | _ -> if Unify.unify state.unifier wanted actual_type then None else refuse ())

let coerce state env ?argument ?takes_view_as_owner (value : Syntax.expression) ~actual ~expected =
  convert state env ?argument ?takes_view_as_owner ~expression:value.id
    (State.read_span state value.id) ~actual ~expected

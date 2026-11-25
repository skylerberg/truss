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

let list_copy_fixes (state : State.state) (written : Syntax.expression) ~view ~owner =
  let is_copyable =
    State.decide_property state Interface.Properties.Copyable owner = Interface.Properties.Holds
  in
  let is_view_of_owner =
    match Types.find_viewed (State.normalize state view) with
    | Some viewed -> State.unify ~modulo_views:true state viewed owner
    | None -> false
  in
  if not (is_copyable && is_view_of_owner) then []
  else
    let title = "Copy the view with `copy()`." in
    let span = State.read_span state written.id in
    let is_postfix (value : Syntax.expression) =
      match value.kind with
      | Name _ | Member _ | Call _ | Bracket _ | Parenthesized _ | Self_value -> true
      | _ -> false
    in
    match written.kind with
    | Mode (_, inner) when is_postfix inner ->
        [ State.fix title [ State.insert (State.read_span state inner.id).stop ".copy()" ] ]
    | _ when is_postfix written -> [ State.fix title [ State.insert span.stop ".copy()" ] ]
    | _ ->
        [
          State.fix title
            [ State.replace span (Printf.sprintf "(%s).copy()" (State.quote_span state span)) ];
        ]

let convert_scalar_or_function (state : State.state) (env : State.env)
    ?(expression : Syntax.expression option) (span : Source.Definition_span.t) ~is_argument ~is_read
    ~refuse ~actual ~expected ~actual_type ~wanted =
  match (actual_type, wanted, expression) with
  | Types.Never, _, _ -> Some (Tables.From_never, expected)
  | Types.Integer, _, Some _
    when is_argument && env.specification && State.is_within state wanted Types.integer_types ->
      Some (Tables.From_integer, expected)
  | _, Types.Integer, _
    when env.specification && State.is_within state actual_type Types.integer_types ->
      Some (Tables.To_integer, expected)
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
                  Failures.report_mismatch state span
                    ~expected:(State.finalize_type state expected)
                    ~actual:(State.finalize_type state actual));
            }
            :: state.capability_constraints;
        Some (Tables.Function_widening, expected)
      end
      else refuse ()
  | _ -> if State.unify ~modulo_views:is_read state wanted actual_type then None else refuse ()

let convert (state : State.state) (env : State.env) ?argument
    ?(expression : Syntax.expression option) (span : Source.Definition_span.t) ~actual ~expected =
  let record_conversions conversions =
    match expression with
    | Some (written : Syntax.expression) ->
        state.tables.conversions.(written.id) <- state.tables.conversions.(written.id) @ conversions
    | None -> ()
  in
  let actual_type = read_head state ~default_at:span actual in
  let wanted = read_expected_head state expected in
  let is_read = argument = Some Language.Mode.Read in
  let refuse () =
    let is_view_of_wanted () =
      match Types.find_viewed actual_type with
      | Some viewed -> State.unify ~modulo_views:true state viewed wanted
      | None -> false
    in
    if argument = Some Language.Mode.Mut && is_view_of_wanted () then
      State.report state Wrong_mode span
        "This is a view, and a view is read-only, so it cannot be passed `mut`. Pass the place \
         that it views."
    else begin
      let fixes =
        match expression with
        | Some written -> list_copy_fixes state written ~view:actual_type ~owner:wanted
        | None -> []
      in
      Failures.report_mismatch ~fixes state span ~expected ~actual
    end;
    None
  in
  let is_known : Types.ty -> bool = function
    | Variable _ | Error _ | Hole | Never -> false
    | Named _ | Parameter _ | Projection _ | Function _ | Integer -> true
  in
  let find_list_of_array ~wanted_list =
    match Types.find_list_of_array actual_type with
    | Some list when Types.is_well_known List (read_expected_head state wanted_list) -> Some list
    | _ -> None
  in
  match Types.find_viewed wanted with
  | Some viewed when is_known actual_type && not (Types.is_view actual_type) -> (
      match find_list_of_array ~wanted_list:viewed with
      | Some list ->
          if State.unify ~modulo_views:true state viewed list then
            record_conversions [ (Tables.Array_as_list, list); (Tables.To_view, expected) ]
          else ignore (refuse ())
      | None ->
          if State.unify ~modulo_views:true state viewed actual_type then
            record_conversions [ (Tables.To_view, expected) ]
          else ignore (refuse ()))
  | _ -> (
      match
        match argument with
        | Some (Read | Mut) -> find_list_of_array ~wanted_list:wanted
        | Some Own | None -> None
      with
      | Some list ->
          if State.unify ~modulo_views:is_read state wanted list then
            record_conversions [ (Tables.Array_as_list, expected) ]
          else ignore (refuse ())
      | None ->
          record_conversions
            (Option.to_list
               (convert_scalar_or_function state env ?expression span
                  ~is_argument:(Option.is_some argument) ~is_read ~refuse ~actual ~expected
                  ~actual_type ~wanted)))

let coerce state env ?argument (value : Syntax.expression) ~actual ~expected =
  convert state env ?argument ~expression:value (State.read_span state value.id) ~actual ~expected

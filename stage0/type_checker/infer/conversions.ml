let read_head (state : State.state) ?default_at type_ =
  match State.normalize state type_ with
  | Types.Variable root ->
      Solver.solve_head state ?default_at root;
      State.normalize state type_
  | head -> head

let read_expected_head state type_ = read_head state type_

let read_actual_head state (value : Syntax.expression) type_ =
  read_head state ~default_at:(Written value.id) type_

let read_checked_head state env (value : Syntax.expression) =
  read_actual_head state value (Hooks.check_expression state env value)

let find_view_as ~owned ~view =
  match (Types.find_view owned, view) with
  | Some (Types.Named { path; _ } as owned_view), Types.Named { path = view_path; _ }
    when Path.equal path view_path ->
      Some owned_view
  | _ -> None

let find_view_copy (state : State.state) (written : Syntax.expression) ~view ~owner :
    Catalog.Inference.view_copy option =
  let copy =
    match State.normalize state owner with
    | Types.Named { path; arguments = [] } when Well_known.is String path -> Some "to_string"
    | Types.Named { path; arguments = [ Type element ] }
      when Well_known.is List path
           && State.decide_property state Interface.Properties.Copyable element = Holds ->
        Some "to_list"
    | _ -> None
  in
  let is_view_of_owner =
    match Types.find_view (State.normalize state owner) with
    | Some owned_view -> Types.equal owned_view (State.normalize state view)
    | None -> false
  in
  match copy with
  | Some copy_method when is_view_of_owner ->
      let is_postfix (value : Syntax.expression) =
        match value.kind with
        | Name _ | Member _ | Call _ | Bracket _ | Parenthesized _ | Self_value -> true
        | _ -> false
      in
      Some
        {
          copy_method;
          edit =
            (match written.kind with
            | Call ({ kind = Member (_, name); _ }, []) when name.text = "copy" ->
                Rename_copy (Written name.id)
            | Mode (_, inner) when is_postfix inner -> Append_copy (Written inner.id)
            | _ when is_postfix written -> Append_copy (Written written.id)
            | _ -> Wrap_copy (Written written.id));
        }
  | _ -> None

let convert (state : State.state) (env : State.env) ?argument ?(takes_view_as_owner = false)
    ?(expression : Syntax.expression option) at ~actual ~expected =
  let is_argument = Option.is_some argument in
  let record_conversion conversion =
    match (conversion, expression) with
    | Some conversion, Some (written : Syntax.expression) ->
        state.tables.conversions.(written.id) <-
          state.tables.conversions.(written.id) @ [ (conversion, expected) ]
    | _ -> ()
  in
  record_conversion
  @@
  let actual_type = read_head state ~default_at:at actual in
  let wanted = read_expected_head state expected in
  let refuse () =
    let copy =
      Option.bind expression (fun written ->
          find_view_copy state written ~view:actual_type ~owner:wanted)
    in
    Failures.report_mismatch ?copy state at ~expected ~actual;
    None
  in
  let between_owner_and_view =
    match if is_argument then find_view_as ~owned:actual_type ~view:wanted else None with
    | Some view -> Some (Tables.Owned_to_view, wanted, view)
    | None when takes_view_as_owner -> (
        match wanted with
        | Types.Named { path; _ } when Well_known.is List path || Well_known.is String path ->
            Option.map
              (fun view -> (Tables.View_to_owned, actual_type, view))
              (find_view_as ~owned:wanted ~view:actual_type)
        | _ -> None)
    | None -> None
  in
  match between_owner_and_view with
  | Some (conversion, written_view, view) ->
      if not (Unify.unify state.unifier written_view view) then
        Failures.report_mismatch state at ~expected ~actual;
      Some conversion
  | None -> (
      match (actual_type, wanted, expression) with
      | Types.Never, _, _ -> Some Tables.From_never
      | Types.Integer, _, Some _
        when is_argument && env.specification && State.is_within state wanted Types.integer_types ->
          Some Tables.From_integer
      | _, Types.Integer, _
        when env.specification && State.is_within state actual_type Types.integer_types ->
          Some Tables.To_integer
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
                      Failures.report_mismatch state at
                        ~expected:(State.finalize_type state expected)
                        ~actual:(State.finalize_type state actual));
                }
                :: state.capability_constraints;
            Some Tables.Function_widening
          end
          else refuse ()
      | _ -> if Unify.unify state.unifier wanted actual_type then None else refuse ())

let coerce state env ?argument ?takes_view_as_owner (value : Syntax.expression) ~actual ~expected =
  convert state env ?argument ?takes_view_as_owner ~expression:value (Written value.id) ~actual
    ~expected

let rec find_offending_expression (state : State.state) (value : Syntax.expression) :
    Syntax.expression option =
  let find_first = List.find_map (find_offending_expression state) in
  let is_built_in (operand : Syntax.expression) =
    match state.tables.types.(operand.id) with
    | Some type_ ->
        Types.is_integer_type type_ || Types.is_float_type type_ || Types.is_builtin Bool type_
        || Types.is_error type_
    | None -> true
  in
  match value.kind with
  | Integer _ | Float _ | True | False | Todo | Expression_error -> None
  | String { rest = []; _ } -> None
  | String { rest = (interpolated, _) :: _; _ } -> Some interpolated
  | Parenthesized inner -> find_offending_expression state inner
  | Prefix (_, inner) ->
      if is_built_in inner then find_offending_expression state inner else Some value
  | Binary { left; right; _ } ->
      if is_built_in left && is_built_in right then find_first [ left; right ] else Some value
  | Name _ | Member _ | Bracket _ -> (
      match (state.tables.resolutions.(value.id), value.kind) with
      | Some (Global _ | Variant_value _ | Type_name _), _ -> None
      | Some (Field_access _), Member (base, _) -> find_offending_expression state base
      | _ -> Some value)
  | Call (_, arguments) -> (
      match state.tables.calls.(value.id) with
      | Some { callee = Constructor _; _ } ->
          find_first (List.map (fun (argument : Syntax.argument) -> argument.value) arguments)
      | _ -> Some value)
  | List items -> find_first items
  | Map entries -> find_first (List.concat_map (fun (key, item) -> [ key; item ]) entries)
  | _ -> Some value

let rec check_arithmetic (state : State.state) (value : Syntax.expression) =
  let evaluate part =
    Interface.Constants.evaluate_expression state.lookups.interface ~visiting:[] state.resolved part
  in
  (match (value.kind, state.tables.types.(value.id)) with
  | Prefix (Negate, { kind = Integer _; _ }), _ -> ()
  | (Prefix _ | Binary _), Some type_ -> (
      match (Types.find_integer_range type_, evaluate value, value.kind) with
      | Some (low, high), Some constant, _ when Z.lt constant low || Z.gt constant high ->
          State.report state Constant_overflow (State.read_span state value.id)
            (Printf.sprintf "This is %s, which does not fit in `%s`, which holds %s to %s."
               (Z.to_string constant) (Types.show type_) (Z.to_string low) (Z.to_string high))
      | Some _, None, Binary { operator = Operation (Arithmetic (Divide | Remainder)); right; _ }
        when evaluate right = Some Z.zero ->
          State.report state Constant_overflow (State.read_span state right.id)
            "This divides by zero."
      | _ -> ())
  | _ -> ());
  Syntax_walk.visit_expression_parts ~on_expression:(check_arithmetic state) ~on_statement:ignore
    value

let check state ~default (value : Syntax.expression) =
  (match find_offending_expression state value with
  | Some part ->
      if default then
        State.report state Default_not_constant (State.read_span state part.id)
          "A default must be a constant expression: literals, arithmetic, constants, and records, \
           variants, and collections built from them. It cannot call a function or name a \
           parameter."
      else
        State.report state Not_constant (State.read_span state part.id)
          "A constant must be a constant expression: literals, arithmetic, other constants, and \
           records, variants, and collections built from them. It cannot call a function."
  | None -> ());
  check_arithmetic state value

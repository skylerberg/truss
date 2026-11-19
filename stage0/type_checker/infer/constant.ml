let read_final_type (state : State.state) (value : Syntax.expression) =
  Option.map (State.finalize_type state) state.tables.types.(value.id)

let rec find_offending_expression (state : State.state) (value : Syntax.expression) :
    Syntax.expression option =
  let find_first = List.find_map (find_offending_expression state) in
  let is_built_in (operand : Syntax.expression) =
    match read_final_type state operand with
    | Some type_ ->
        Types.is_integer_type type_ || Types.is_float_type type_ || Types.is_builtin Bool type_
        || Types.is_error type_
    | None -> true
  in
  let is_rejected (expression : Syntax.expression) =
    match read_final_type state expression with Some type_ -> Types.is_error type_ | None -> false
  in
  match value.kind with
  | _ when is_rejected value -> None
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

let report_failure (state : State.state) type_ (value : Syntax.expression)
    (failure : Interface.Integer_arithmetic.failure) =
  let report (at : Syntax.expression) message =
    State.report state Constant_overflow (State.read_span state at.id) message
  in
  match (failure, value.kind, Types.find_integer_range type_) with
  | Out_of_range result, _, Some (low, high) ->
      report value
        (Printf.sprintf "This is %s, which does not fit in `%s`, which holds %s to %s."
           (Z.to_string result) (Types.show type_) (Z.to_string low) (Z.to_string high))
  | Zero_divisor, Binary { right; _ }, _ -> report right "This divides by zero."
  | Least_value_over_minus_one, _, _ ->
      report value
        (Printf.sprintf "This overflows `%s`: the least value over -1." (Types.show type_))
  | Shift_too_large amount, Binary { right; _ }, _ ->
      report right
        (Printf.sprintf "This shifts a `%s` by %s, which is not less than its %d bits."
           (Types.show type_) (Z.to_string amount)
           (match Types.find_integer_bits type_ with
           | Some (bits, _) -> bits
           | None -> State.raise_bug "a shift of `%s`, which has no width" (Types.show type_)))
  | (Out_of_range _ | Zero_divisor | Shift_too_large _), _, _ ->
      State.raise_bug "the failure of `%s` does not match its operation"
        (State.quote_span state (State.read_span state value.id))

let rec check_arithmetic (state : State.state) (value : Syntax.expression) =
  (match (value.kind, read_final_type state value) with
  | Prefix (Negate, { kind = Integer _; _ }), _ -> ()
  | (Prefix _ | Binary _), Some type_ -> (
      match
        Interface.Constants.evaluate_expression state.lookups.interface state.resolved type_ value
      with
      | Fails (failure, at) when at.id = value.id -> report_failure state type_ value failure
      | Folded _ | Not_folded | Fails _ | Depends_on_failure -> ())
  | _ -> ());
  Syntax_walk.visit_expression_parts ~on_expression:(check_arithmetic state) ~on_statement:ignore
    value

let check state ~default (value : Syntax.expression) =
  State.check_when_final state @@ fun () ->
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

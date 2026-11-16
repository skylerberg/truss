open Syntax
open State

let rec offending state (value : expression) : expression option =
  let first = List.find_map (offending state) in
  let built_in (operand : expression) =
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
  | Parenthesized inner -> offending state inner
  | Prefix (_, inner) -> if built_in inner then offending state inner else Some value
  | Binary { left; right; _ } ->
      if built_in left && built_in right then first [ left; right ] else Some value
  | Name _ | Member _ | Bracket _ -> (
      match (state.tables.resolutions.(value.id), value.kind) with
      | Some (Global _ | Variant_value _ | Type_name _), _ -> None
      | Some (Field_access _), Member (base, _) -> offending state base
      | _ -> Some value)
  | Call (_, arguments) -> (
      match state.tables.calls.(value.id) with
      | Some { callee = Constructor _; _ } ->
          first (List.map (fun (argument : argument) -> argument.value) arguments)
      | _ -> Some value)
  | List items -> first items
  | Map entries -> first (List.concat_map (fun (key, item) -> [ key; item ]) entries)
  | _ -> Some value

let rec check_arithmetic state (value : expression) =
  let worked_out part =
    Interface.Constants.evaluate_expression state.lookups.interface ~visiting:[] state.resolved part
  in
  (match (value.kind, state.tables.types.(value.id)) with
  | Prefix (Negate, { kind = Integer _; _ }), _ -> ()
  | (Prefix _ | Binary _), Some type_ -> (
      match (Types.find_integer_range type_, worked_out value, value.kind) with
      | Some (low, high), Some constant, _ when Z.lt constant low || Z.gt constant high ->
          report state Constant_overflow (read_span state value.id)
            (Printf.sprintf "This is %s, which does not fit in `%s`, which holds %s to %s."
               (Z.to_string constant) (Types.show type_) (Z.to_string low) (Z.to_string high))
      | Some _, None, Binary { operator = Operation (Arithmetic (Divide | Remainder)); right; _ }
        when worked_out right = Some Z.zero ->
          report state Constant_overflow (read_span state right.id) "This divides by zero."
      | _ -> ())
  | _ -> ());
  Syntax_walk.expression_parts ~expression:(check_arithmetic state) ~statement:ignore value

let check state ~default (value : expression) =
  (match offending state value with
  | Some part ->
      if default then
        report state Default_not_constant (read_span state part.id)
          "A default must be a constant expression: literals, arithmetic, constants, and records, \
           variants, and collections built from them. It cannot call a function or name a \
           parameter."
      else
        report state Not_constant (read_span state part.id)
          "A constant must be a constant expression: literals, arithmetic, other constants, and \
           records, variants, and collections built from them. It cannot call a function."
  | None -> ());
  check_arithmetic state value

let read_final_type (state : State.state) (value : Syntax.expression) =
  Option.map (State.finalize_type state) state.tables.types.(value.id)

let rec find_offending_expression (state : State.state) ~may_call (value : Syntax.expression) :
    Syntax.expression option =
  let find_first = List.find_map (find_offending_expression state ~may_call) in
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
  let find_in_resolved () =
    match (state.tables.resolutions.(value.id), value.kind) with
    | Some (Global _ | Variant_value _ | Type_name _), _ -> None
    | Some (Field_access _), Member (base, _) -> find_first [ base ]
    | _ -> Some value
  in
  match value.kind with
  | _ when is_rejected value -> None
  | Integer _ | Float _ | True | False | Todo | Expression_error -> None
  | String { rest = []; _ } -> None
  | String { rest; _ } when may_call -> find_first (List.map fst rest)
  | String { rest = (interpolated, _) :: _; _ } -> Some interpolated
  | Parenthesized inner -> find_first [ inner ]
  | Prefix (_, inner) -> if may_call || is_built_in inner then find_first [ inner ] else Some value
  | Binary { left; right; _ } ->
      if may_call || (is_built_in left && is_built_in right) then find_first [ left; right ]
      else Some value
  | Bracket (base, items) when may_call && state.resolved.brackets.(value.id) <> Some Type_arguments
    ->
      find_first
        (base
        :: List.concat_map
             (function
               | Syntax.Item { kind = Range { start; stop; _ }; _ } ->
                   Option.to_list start @ Option.to_list stop
               | Item index -> [ index ]
               | Item_constraint _ -> [])
             items)
  | Name _ | Member _ | Bracket _ -> find_in_resolved ()
  | Call (_, arguments) -> (
      match Tables.find_call state.tables value.id with
      | Some { callee = Constructor _; _ } ->
          find_first (List.map (fun (argument : Syntax.argument) -> argument.value) arguments)
      | Some
          { callee = Function _ | Trait_method _ | Capability_method _ | Intrinsic _; arguments; _ }
        when may_call ->
          find_first (List.map (fun (argument : Tables.argument) -> argument.expression) arguments)
      | _ -> Some value)
  | List items -> find_first items
  | Map entries -> find_first (List.concat_map (fun (key, item) -> [ key; item ]) entries)
  | _ -> Some value

let rec check_arithmetic (state : State.state) (value : Syntax.expression) =
  let evaluate part =
    Interface.Constants.evaluate_expression state.lookups.interface ~visiting:[] state.resolved part
  in
  (match (value.kind, read_final_type state value) with
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
  State.check_when_final state @@ fun () ->
  (match find_offending_expression state ~may_call:(not default) value with
  | Some part ->
      if default then
        State.report state Default_not_constant (State.read_span state part.id)
          "A default must be a constant expression: literals, arithmetic, constants, and records, \
           variants, and collections built from them. It cannot call a function or name a \
           parameter."
      else
        State.report state Not_constant (State.read_span state part.id)
          "The value of a constant is made of literals, other constants, operators, calls, and the \
           records, variants, collections, and strings built from them. Move this into a function, \
           and call the function here."
  | None -> ());
  check_arithmetic state value

let rec find_part_that_is_not_data (state : State.state) ~visited (type_ : Types.ty) =
  match State.normalize state type_ with
  | Function _ -> Some "a function type"
  | Any _ -> Some "an `any` type"
  | Named { path; arguments } as named -> (
      let find_in_arguments () =
        List.find_map
          (function
            | Types.Type argument -> find_part_that_is_not_data state ~visited argument
            | Value _ -> None)
          arguments
      in
      match Well_known.find_builtin_type path with
      | Some Handle -> Some "a handle"
      | Some Shared -> Some "state that tasks share"
      | Some _ -> find_in_arguments ()
      | None when List.exists (Types.equal named) visited -> None
      | None ->
          let interface = Interface.Definition.read_type_interface state.lookups.interface path in
          let substitution = Types.make_substitution interface.type_generics arguments in
          List.find_map
            (fun field ->
              find_part_that_is_not_data state ~visited:(named :: visited)
                (Types.substitute substitution field))
            (Types.list_field_types interface))
  | Parameter _ | Projection _ | Never | Integer | Variable _ | Hole | Error _ -> None

let check_type (state : State.state) (written : Syntax.type_expression) type_ =
  Option.iter
    (fun part ->
      State.report state Constant_not_data
        (State.read_span state written.id)
        (Printf.sprintf
           "A constant is stored in the compiled program as data, so its type cannot be or hold %s."
           part))
    (find_part_that_is_not_data state ~visited:[] type_)

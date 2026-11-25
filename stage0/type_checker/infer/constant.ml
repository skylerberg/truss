let read_final_type (state : State.state) (value : Syntax.expression) =
  Option.map (State.finalize_type state) state.tables.types.(value.id)

type site = Value | Default | Evaluated_condition

let rec list_bound_locals (pattern : Syntax.pattern) : Syntax.id list =
  let list_field (field : Syntax.pattern_field) =
    match field.kind with
    | Named_field (_, pattern) | Field pattern -> list_bound_locals pattern
    | Rest -> []
  in
  match pattern.kind with
  | Binding name -> [ name.id ]
  | Variant { fields; _ } -> List.concat_map list_field (Option.value fields ~default:[])
  | Record fields -> List.concat_map list_field fields
  | Tuple patterns | Alternatives patterns -> List.concat_map list_bound_locals patterns
  | Wildcard | Qualified_constant _ | Literal _ | Pattern_range _ | Pattern_error -> []

let rec find_offending_expression (state : State.state) ~may_call ~bound (value : Syntax.expression)
    : Syntax.expression option =
  let find_first = List.find_map (find_offending_expression state ~may_call ~bound) in
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
    | Some (Local_value local), _ when List.mem local bound -> None
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
               | Item_constraint _ | Item_type _ -> [])
             items)
  | Range { start; stop; _ } when may_call -> find_first (Option.to_list start @ Option.to_list stop)
  | Quantified { binder = Binder_in (pattern, collection); body; _ } when may_call -> (
      match find_first [ collection ] with
      | Some _ as offending -> offending
      | None ->
          find_offending_expression state ~may_call ~bound:(list_bound_locals pattern @ bound) body)
  | Quantified { binder = Binder_type _; _ } when may_call -> None
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

let mentions_type_parameter state type_ =
  Types.exists ~resolve:(State.finalize_type state)
    (function Types.Parameter _ | Projection _ -> true | _ -> false)
    type_

let rec find_use_of_a_type_parameter (state : State.state) (value : Syntax.expression) :
    Syntax.expression option =
  let uses_one =
    (match read_final_type state value with
      | Some type_ -> mentions_type_parameter state type_
      | None -> false)
    ||
    let instantiates_with_one (instantiation : Types.instantiation) =
      List.exists
        (function
          | Types.Type type_ -> mentions_type_parameter state type_
          | Value (Value_parameter _) -> true
          | Value (Known _ | Value_variable _) -> false)
        instantiation.type_arguments
    in
    match Tables.find_call state.tables value.id with
    | Some { callee = Function { instantiation; _ }; _ } -> instantiates_with_one instantiation
    | Some { callee = Trait_method { instantiation; self_type; _ }; _ } ->
        instantiates_with_one instantiation || mentions_type_parameter state self_type
    | Some _ | None -> false
  in
  let found = ref None in
  Syntax_walk.visit_children
    (fun part -> if Option.is_none !found then found := find_use_of_a_type_parameter state part)
    value;
  match !found with Some _ as part -> part | None -> if uses_one then Some value else None

let rec check_arithmetic (state : State.state) (value : Syntax.expression) =
  let evaluate part =
    Interface.Constants.evaluate_expression state.lookups.interface ~visiting:[] state.resolved part
  in
  (match (value.kind, read_final_type state value) with
  | Prefix (Negate, { kind = Integer _; _ }), _ -> ()
  | (Prefix _ | Binary _), Some type_ -> (
      match (Types.find_integer_range type_, evaluate value, value.kind) with
      | Some (low, high), Some constant, _ when Z.lt constant low || Z.gt constant high ->
          State.report state
            (Constant_out_of_range { at = Written value.id; constant; type_; low; high })
      | Some _, None, Binary { operator = Operation (Arithmetic (Divide | Remainder)); right; _ }
        when evaluate right = Some Z.zero ->
          State.report state (Division_by_zero { at = Written right.id })
      | _ -> ())
  | _ -> ());
  Syntax_walk.visit_expression_parts ~on_expression:(check_arithmetic state) ~on_statement:ignore
    value

let check state (site : site) (value : Syntax.expression) =
  State.check_when_final state @@ fun () ->
  (match find_offending_expression state ~may_call:(site <> Default) ~bound:[] value with
  | Some part -> (
      let at : Core.origin = Written part.id in
      match site with
      | Default -> State.report state (Default_not_constant { at })
      | Value -> State.report state (Not_constant { at })
      | Evaluated_condition -> State.report state (Condition_not_constant { at }))
  | None ->
      if site = Evaluated_condition then
        Option.iter
          (fun (part : Syntax.expression) ->
            State.report state (Condition_names_parameter { at = Written part.id }))
          (find_use_of_a_type_parameter state value));
  check_arithmetic state value

let rec find_part_that_is_not_data (state : State.state) ~visited (type_ : Types.ty) =
  match State.normalize state type_ with
  | Function _ -> Some Catalog.Inference.Function_type
  | Named { path; arguments } as named -> (
      let find_in_arguments () =
        List.find_map
          (function
            | Types.Type argument -> find_part_that_is_not_data state ~visited argument
            | Value _ -> None)
          arguments
      in
      match Well_known.find_builtin_type path with
      | Some Handle -> Some Catalog.Inference.Handle
      | Some Shared -> Some Shared_state
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
    (fun part -> State.report state (Constant_not_data { at = Written written.id; part }))
    (find_part_that_is_not_data state ~visited:[] type_)

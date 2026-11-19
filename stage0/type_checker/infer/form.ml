let build_expression_by_id (state : State.state) (id : Syntax.id) : Core.expression =
  match state.form.expression_builders.(id) with
  | Some build -> build ()
  | None -> State.raise_bug "a call's argument has no core node"

let read_call (state : State.state) (id : Syntax.id) : Tables.call =
  match state.tables.calls.(id) with
  | Some call -> call
  | None -> State.raise_bug "the checker recorded no call for a call node"

let read_evidence state self_type trait : Core.evidence =
  match State.find_evidence state self_type trait with
  | Some (From_impl { impl; substitution }) -> Impl { impl; substitution }
  | Some From_bound -> Bound
  | Some From_any -> Dynamic
  | Some (Built_in | Accepted _) | None ->
      State.raise_bug "`%s` does not implement `%s` by an impl, a bound, or `any`"
        (Types.show self_type) (Types.show_trait trait)

let convert_callee state (callee : Tables.callee) : Core.operand Core.target =
  match callee with
  | Function { path; instantiation } -> Function { path; instantiation }
  | Trait_method { trait; name; receiver; self_type; instantiation } ->
      let evidence = read_evidence state self_type trait in
      Trait_method { trait; name; receiver; self_type; instantiation; evidence }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Constructor _ | Indirect | Built_in_operator -> State.raise_bug "this callee has no core callee"

let build_arguments state (call : Tables.call) : Core.argument list =
  List.init
    (List.length call.arguments + List.length call.omitted_defaults)
    (fun index ->
      match
        List.find_opt
          (fun (argument : Tables.argument) -> argument.core_argument_index = index)
          call.arguments
      with
      | Some argument ->
          Core.Passed
            {
              mode = argument.mode;
              value =
                Operands.build argument.mode (build_expression_by_id state argument.expression);
            }
      | None -> Default)

let build_call state ~lends ?function_value (call : Tables.call) : Core.call =
  State.make_call state
    ~callee:
      (match (call.callee, function_value) with
      | Indirect, Some function_value -> Indirect (Operands.build Read function_value)
      | direct, _ -> convert_callee state direct)
    ~arguments:(build_arguments state call) ~lends

let arithmetic_methods : (Well_known.method_ * Intrinsic.scalar) list =
  [
    (Add_add, Add);
    (Subtract_subtract, Subtract);
    (Multiply_multiply, Multiply);
    (Divide_divide, Divide);
    (Remainder_remainder, Remainder);
    (Negate_negate, Negate);
  ]

let is_number type_ = Types.is_integer_type type_ || Types.is_float_type type_

let is_built_in_scalar type_ =
  is_number type_ || Types.is_builtin Bool type_ || Types.is_builtin Character type_

let find_built_in_operation (trait : Types.trait_reference) name receiver self_type =
  if
    is_number self_type
    && List.for_all (fun argument -> argument = Types.Type self_type) trait.trait_arguments
  then
    Option.bind
      (Well_known.find_method (Method { owner = trait.trait; name; receiver }))
      (fun method_ -> List.assoc_opt method_ arithmetic_methods)
  else None

let build_argument_expressions state (call : Tables.call) =
  List.map
    (fun (argument : Tables.argument) -> build_expression_by_id state argument.expression)
    (List.sort
       (fun (left : Tables.argument) (right : Tables.argument) ->
         compare left.core_argument_index right.core_argument_index)
       call.arguments)

let read_constructor_fields (state : State.state) type_ variant type_arguments =
  let fields =
    match variant with
    | None -> Members.find_fields state.lookups type_ type_arguments
    | Some variant ->
        Option.bind (Members.find_variants state.lookups type_ type_arguments) (fun variants ->
            Option.bind
              (List.find_opt
                 (fun (written : Types.variant) -> written.variant_name = variant)
                 variants)
              (fun (written : Types.variant) -> written.fields))
  in
  match fields with
  | Some fields -> fields
  | None -> State.raise_bug "`%s` is constructed but has no fields" (Path.show type_)

let build_call_kind ?lends ?function_value state (value : Syntax.expression) : Core.kind =
  let recorded = read_call state value.id in
  let lends =
    match lends with Some lends -> Some lends | None -> state.tables.lend_modes.(value.id)
  in
  match recorded.callee with
  | Trait_method { trait; _ } when Well_known.is Copyable trait.trait -> (
      match recorded.arguments with
      | [ receiver ] ->
          Copy (Operands.build Read (build_expression_by_id state receiver.expression))
      | _ -> State.raise_bug "`copy` does not have exactly one argument")
  | Trait_method { trait; name; receiver; self_type; _ }
    when Option.is_some (find_built_in_operation trait name receiver self_type) ->
      Operator
        {
          operation = Option.get (find_built_in_operation trait name receiver self_type);
          arguments = build_argument_expressions state recorded;
        }
  | Trait_method { trait; name; receiver; self_type; _ }
    when is_built_in_scalar self_type
         && Well_known.is_method Equal_equal (Method { owner = trait.trait; name; receiver }) -> (
      match build_argument_expressions state recorded with
      | [ left; right ] -> Compare { comparison = Equal; left; right }
      | _ -> State.raise_bug "`equal` does not have exactly two arguments")
  | Constructor { type_; variant; type_arguments } ->
      let declared = read_constructor_fields state type_ variant type_arguments in
      let written =
        List.map
          (fun (argument : Tables.argument) ->
            ( (List.nth declared argument.core_argument_index).field_name,
              Some (Operands.build argument.mode (build_expression_by_id state argument.expression))
            ))
          recorded.arguments
      in
      let defaulted =
        List.filter_map
          (fun (field : Types.field) ->
            if List.mem_assoc field.field_name written then None else Some (field.field_name, None))
          declared
      in
      Construct { variant; fields = written @ defaulted }
  | Built_in_operator -> State.raise_bug "an operator is recorded as a call"
  | Indirect | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> (
      let function_value = Option.map (State.build_expression state) function_value in
      let call = Core.Call (build_call state ~lends ?function_value recorded) in
      match lends with
      | Some _ ->
          Use
            (Lent
               (State.make_synthetic_expression state ~origin:value.id recorded.callee_result call))
      | None -> call)

let register_call ?function_value state (value : Syntax.expression) =
  State.register_expression state value (fun () -> build_call_kind ?function_value state value)

let register_index state (value : Syntax.expression) =
  State.register_expression state value (fun () ->
      match (read_call state value.id).callee with
      | Trait_method { receiver = Instance Mut; _ } -> build_call_kind ~lends:Mut state value
      | _ -> build_call_kind ~lends:Read state value)

let build_numeric_literal (state : State.state) (id : Syntax.id) : Core.kind =
  match state.tables.literals.(id) with
  | Some (Integer_value number) -> Integer number
  | Some (Float_value number) -> Float number
  | None -> State.raise_bug "a literal has no value"

let read_type (state : State.state) (value : Syntax.expression) =
  match state.tables.types.(value.id) with
  | Some type_ -> type_
  | None ->
      State.raise_bug "`%s` has a core node but no recorded type"
        (State.quote_span state (State.read_span state value.id))

let build_function_value (state : State.state) (value : Syntax.expression) : Core.kind =
  match state.tables.resolutions.(value.id) with
  | Some (Global { path; instantiation }) -> Function_value { path; instantiation }
  | _ ->
      State.raise_bug "`%s` is not recorded as a function"
        (State.quote_span state (State.read_span state value.id))

let build_variant_value state (value : Syntax.expression) type_path variant : Core.kind =
  match read_type state value with
  | Types.Function { output = Types.Named { arguments; _ } as variant_type; _ } ->
      let fields =
        List.map
          (fun (field : Types.field) -> (field, State.allocate_synthetic_local state))
          (read_constructor_fields state type_path (Some variant) arguments)
      in
      Lambda
        {
          parameters =
            List.map
              (fun ((field : Types.field), local) : Core.pattern ->
                {
                  id = State.allocate_node_id state;
                  origin = value.id;
                  type_ = field.field_type;
                  kind = Bind { local; is_var = false; mode = Own };
                })
              fields;
          captures = [];
          body =
            {
              statements = [];
              value =
                Some
                  (State.make_synthetic_expression state ~origin:value.id variant_type
                     (Construct
                        {
                          variant = Some variant;
                          fields =
                            List.map
                              (fun ((field : Types.field), local) ->
                                ( field.field_name,
                                  Some
                                    (Core.Value
                                       (State.make_synthetic_expression state ~origin:value.id
                                          field.field_type
                                          (Core.Use
                                             (Local
                                                {
                                                  local;
                                                  type_ = field.field_type;
                                                  origin = value.id;
                                                })))) ))
                              fields;
                        }));
            };
          result = variant_type;
        }
  | _ -> Construct { variant = Some variant; fields = [] }

let read_local_type (state : State.state) (id : Syntax.id) =
  match state.tables.local_types.(id) with
  | Some type_ -> type_
  | None -> State.raise_bug "a local has no recorded type"

let build_declared_local (state : State.state) (id : Syntax.id) : Core.local =
  match Hashtbl.find_opt state.locals id with
  | Some local -> Declared { origin = id; name = local.name }
  | None -> State.raise_bug "a local that nothing declares"

let build_declared_place state ~origin (id : Syntax.id) : Core.place =
  Local { local = build_declared_local state id; type_ = read_local_type state id; origin }

let build_local_use state ~origin (id : Syntax.id) : Core.kind =
  if State.was_hole state (fun tables -> tables.local_types) id then Todo
  else Use (build_declared_place state ~origin id)

let read_self_type state (env : State.env) =
  match env.self with
  | Some type_ -> State.finalize_type state type_
  | None -> State.raise_bug "`self` is used outside a method"

let build_self_local state (env : State.env) ~origin : Core.place =
  Local { local = Self; type_ = read_self_type state env; origin }

let build_constant_place (state : State.state) ~origin (path : Path.t) : Core.place =
  Constant
    { path; type_ = Interface.Definition.read_constant_type state.lookups.interface path; origin }

let build_record fields : Core.kind =
  Construct
    {
      variant = None;
      fields =
        List.map
          (fun (field, value) -> (Well_known.show_field field, Some (Operands.build Own value)))
          fields;
    }

let build_range_record state (value : Syntax.expression) start stop ~inclusive : Core.kind =
  match (start, stop) with
  | Some start, Some stop ->
      let start = State.build_expression state start in
      let stop = State.build_expression state stop in
      let inclusive =
        State.make_synthetic_expression state ~origin:value.id Types.bool (Core.Boolean inclusive)
      in
      build_record [ (Range_start, start); (Range_stop, stop); (Range_inclusive, inclusive) ]
  | _ -> State.raise_bug "a range without both bounds is valid only inside a slice"

let list_capability_impls (state : State.state) (type_ : Types.ty) =
  match type_ with
  | Types.Named { path; _ } ->
      List.filter_map
        (fun (trait, _) ->
          if Resolve.Names.find_kind state.lookups.interface.names trait = Some Capability then
            match
              State.find_evidence state type_ (State.make_trait_reference ~arguments:[] trait)
            with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ Core.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Definition.find_impl_interface state.lookups.interface impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Interface.Impls.list_impls_for_type state.lookups.interface path package)
           (List.sort_uniq compare
              [ Path.locate_package path; state.package; Path.standard_package ]))
  | _ -> []

let build_provide state (implementations : Syntax.expression list) (body : Syntax.block) : Core.kind
    =
  let implementations =
    List.map
      (fun (implementation : Syntax.expression) : Core.implementation ->
        let mode : Language.Mode.t =
          match implementation.kind with Mode (Mut, _) -> Mut | _ -> Read
        in
        let node = State.build_expression state implementation in
        {
          origin = implementation.id;
          mode;
          value = Operands.build mode node;
          type_ = node.type_;
          provides = List.map fst (list_capability_impls state node.type_);
        })
      implementations
  in
  Provide { implementations; body = State.build_block state body }

let push_target : Core.operand Core.target =
  Function
    { path = Well_known.make_method_path String_push; instantiation = Types.no_instantiation }

let read_template (state : State.state) (literal : Syntax.string_literal) =
  match state.tables.templates.(literal.id) with
  | Some template -> template
  | None -> State.raise_bug "the checker recorded no template for a string literal"

let build_untagged_string state ~origin (literal : Syntax.string_literal) : Core.kind =
  match literal.rest with
  | [] -> String literal.first.value
  | rest ->
      let make = State.make_synthetic_expression state ~origin in
      let make_statement kind : Core.statement =
        { id = State.allocate_node_id state; origin; kind }
      in
      let text = State.allocate_synthetic_local state in
      let text_place : Core.place = Local { local = text; type_ = State.string_type; origin } in
      let let_text =
        make_statement
          (Let
             {
               pattern =
                 {
                   id = State.allocate_node_id state;
                   origin;
                   type_ = State.string_type;
                   kind = Bind { local = text; is_var = true; mode = Own };
                 };
               value = Operands.build Own (make State.string_type (String literal.first.value));
               else_ = None;
             })
      in
      let push (pushed : Syntax.text) =
        if pushed.value = "" then []
        else
          [
            make_statement
              (Evaluate
                 (make Types.unit
                    (Call
                       (State.make_call state ~callee:push_target
                          ~arguments:
                            [
                              Passed { mode = Mut; value = Place text_place };
                              Passed
                                {
                                  mode = Read;
                                  value =
                                    Value
                                      (make
                                         (Types.make_named (Well_known.make_path String_slice) [])
                                         (String pushed.value));
                                };
                            ]
                          ~lends:None))));
          ]
      in
      let make_display part (conversion : Tables.call option) =
        match conversion with
        | Some recorded ->
            make_statement
              (Evaluate
                 (make Types.unit
                    (Call
                       (State.make_call state
                          ~callee:(convert_callee state recorded.callee)
                          ~arguments:
                            [
                              Operands.build_argument Read (State.build_expression state part);
                              Passed { mode = Mut; value = Place text_place };
                            ]
                          ~lends:None))))
        | None -> State.raise_bug "an interpolated value has no `display`"
      in
      Block
        {
          statements =
            let_text
            :: List.concat
                 (List.map2
                    (fun (part, after) conversion -> make_display part conversion :: push after)
                    rest (read_template state literal).part_conversions);
          value = Some (make State.string_type (Use text_place));
        }

let build_list_literal state ~origin (element : Types.ty) (elements : Core.expression list) :
    Core.kind =
  let make = State.make_synthetic_expression state ~origin in
  let storage_type = Types.make_builtin Storage ~arguments:[ Type element ] in
  let make_storage operation ~type_arguments arguments =
    make storage_type
      (Call
         (State.make_call state
            ~callee:(Intrinsic { operation; type_arguments })
            ~arguments ~lends:None))
  in
  let storage =
    match elements with
    | [] ->
        make_storage (Buffer Storage_with_capacity) ~type_arguments:[ Types.Type element ]
          [ Operands.build_argument Read (make (Types.make_builtin UInt64) (Integer Z.zero)) ]
    | _ ->
        let count = Types.Value (Known (Z.of_int (List.length elements))) in
        let array =
          make
            (Types.make_builtin Array ~arguments:[ Type element; count ])
            (Collection_literal { elements; construction = Array })
        in
        make_storage (Buffer Storage_from_array) ~type_arguments:[ Types.Type element; count ]
          [ Operands.build_argument Own array ]
  in
  Call
    (State.make_call state
       ~callee:
         (Function
            {
              path = Well_known.make_method_path List_from_storage;
              instantiation =
                { Types.no_instantiation with type_arguments = [ Types.Type element ] };
            })
       ~arguments:[ Passed { mode = Own; value = Value storage } ]
       ~lends:None)

let build_tagged_string state (value : Syntax.expression) (literal : Syntax.string_literal)
    ~(part : Types.ty) : Core.kind =
  let recorded = read_template state literal in
  let from_template =
    match recorded.from_template with
    | Some call -> call
    | None -> State.raise_bug "a tagged string has no `from_template`"
  in
  let make = State.make_synthetic_expression state ~origin:value.id in
  let make_list element elements =
    make
      (Types.make_named (Well_known.make_path List) [ element ])
      (build_list_literal state ~origin:value.id element elements)
  in
  let literal_type = Types.make_named (Well_known.make_path Literal) [] in
  let texts =
    List.map
      (fun (written : Syntax.text) ->
        make literal_type
          (build_record
             [
               ( Literal_text,
                 make
                   (Types.make_named (Well_known.make_path String_slice) [])
                   (String written.value) );
             ]))
      (literal.first :: List.map snd literal.rest)
  in
  let parts =
    List.map2
      (fun ((written : Syntax.expression), _) (conversion : Tables.call option) ->
        match conversion with
        | Some call ->
            State.make_synthetic_expression state ~origin:written.id call.callee_result
              (Call (build_call state ~lends:None call))
        | None -> State.build_expression state written)
      literal.rest recorded.part_conversions
  in
  let texts = make_list literal_type texts in
  let template =
    make
      (Types.make_named (Well_known.make_path Template) [ part ])
      (build_record [ (Template_literals, texts); (Template_parts, make_list part parts) ])
  in
  Template
    {
      literals =
        List.map
          (fun (written : Syntax.text) -> written.value)
          (literal.first :: List.map snd literal.rest);
      call =
        make from_template.callee_result
          (Call
             (State.make_call state
                ~callee:(convert_callee state from_template.callee)
                ~arguments:[ Operands.build_argument Read template ]
                ~lends:None));
    }

let read_pattern_type (state : State.state) (id : Syntax.id) =
  match state.tables.scrutinee_types.(id) with
  | Some type_ -> type_
  | None -> State.raise_bug "a pattern has no recorded type"

let build_constant_pattern state (id : Syntax.id) (value : Core.pattern_constant) :
    Core.pattern_kind =
  let type_ = read_pattern_type state id in
  if is_built_in_scalar type_ then Literal value
  else
    let { Well_known.owner; name; receiver } = Well_known.locate_method Equal_equal in
    let equal = State.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
    Equal_to
      {
        value;
        equal =
          State.make_callee state
            (Trait_method
               {
                 trait = equal;
                 name;
                 receiver;
                 self_type = type_;
                 instantiation = Types.no_instantiation;
                 evidence = read_evidence state type_ equal;
               });
      }

let read_constant_path (state : State.state) (id : Syntax.id) =
  match state.tables.patterns.(id) with
  | Some (Constant_pattern path) -> path
  | _ -> State.raise_bug "a pattern names a constant that was not recorded"

let build_named_constant state (id : Syntax.id) : Core.pattern_constant =
  Named_constant (read_constant_path state id)

let build_literal_constant (state : State.state) (id : Syntax.id) (written : Syntax.literal) :
    Core.pattern_constant =
  match (written, state.tables.literals.(id)) with
  | _, Some (Integer_value number) -> Integer_constant number
  | Literal_true, _ -> Boolean_constant true
  | Literal_false, _ -> Boolean_constant false
  | Literal_string text, _ -> String_constant text.first.value
  | Literal_integer _, _ -> State.raise_bug "an integer pattern has no value"

let build_range_bound (state : State.state) (bound : Syntax.range_end) : Core.range_bound =
  match bound.kind with
  | End_literal _ -> (
      match state.tables.literals.(bound.id) with
      | Some (Integer_value number) -> Integer_bound number
      | Some (Float_value _) | None -> State.raise_bug "a range bound has no integer value")
  | End_constant _ -> Constant_bound (read_constant_path state bound.id)

let build_pattern_fields state (fields : Types.field list)
    (matched : (string * Syntax.pattern) list) =
  List.filter_map
    (fun (field : Types.field) ->
      Option.map
        (fun written -> (field.field_name, State.build_pattern state written))
        (List.assoc_opt field.field_name matched))
    fields

let convert_to_integer state (node : Core.expression) : Core.expression =
  if not (State.is_within state node.type_ Types.integer_types) then node
  else
    State.make_synthetic_expression state ~origin:node.origin Types.Integer
      (Convert { conversion = To_integer; value = node })

let convert_to_operation : Syntax.operation -> Intrinsic.scalar = function
  | Arithmetic Add -> Add
  | Arithmetic Subtract -> Subtract
  | Arithmetic Multiply -> Multiply
  | Arithmetic Divide -> Divide
  | Arithmetic Remainder -> Remainder
  | Bitwise Bit_and -> Bit_and
  | Bitwise Bit_or -> Bit_or
  | Bitwise Bit_xor -> Bit_xor
  | Shift Shift_left -> Shift_left
  | Shift Shift_right -> Shift_right

let build_operator state (value : Syntax.expression) operation (operands : Syntax.expression list) :
    Core.kind =
  let arguments = List.map (State.build_expression state) operands in
  Operator
    {
      operation;
      arguments =
        (if read_type state value = Types.Integer then List.map (convert_to_integer state) arguments
         else arguments);
    }

let build_built_in_comparison state comparison (left : Syntax.expression)
    (right : Syntax.expression) : Core.kind =
  let left = State.build_expression state left in
  let right = State.build_expression state right in
  let left, right =
    if Types.equal left.type_ right.type_ then (left, right)
    else (convert_to_integer state left, convert_to_integer state right)
  in
  Compare { comparison; left; right }

let build_comparison state (value : Syntax.expression) comparison (left : Syntax.expression)
    (right : Syntax.expression) : Core.kind =
  let recorded = read_call state value.id in
  match recorded.callee with
  | Trait_method { self_type; _ } when is_built_in_scalar self_type ->
      build_built_in_comparison state comparison left right
  | _ -> (
      let call =
        State.make_synthetic_expression state ~origin:value.id recorded.callee_result
          (Call (build_call state ~lends:None recorded))
      in
      let make_matches_variant variant : Core.kind =
        Matches
          {
            value = Operands.build Own call;
            pattern =
              {
                id = State.allocate_node_id state;
                origin = value.id;
                type_ = recorded.callee_result;
                kind = Variant { variant = Well_known.show_variant variant; fields = [] };
              };
          }
      in
      let make_not kind : Core.kind =
        Not (State.make_synthetic_expression state ~origin:value.id Types.bool kind)
      in
      match comparison with
      | Equal -> call.kind
      | Not_equal -> Not call
      | Less -> make_matches_variant Ordering_less
      | Less_equal -> make_not (make_matches_variant Ordering_greater)
      | Greater -> make_matches_variant Ordering_greater
      | Greater_equal -> make_not (make_matches_variant Ordering_less))

let binds_lent_part state (condition : Core.expression) =
  let may_alias (pattern : Core.pattern) =
    match pattern.kind with
    | Bind { mode = Mut; _ } -> true
    | Bind { mode = Read | Own; _ } ->
        State.is_view state pattern.type_ || not (State.is_plain state pattern.type_)
    | Wildcard | Variant _ | Record _ | Alternatives _ | Literal _ | Range _ | Equal_to _ -> false
  in
  let is_lent (place : Core.place) = match place with Lent _ -> true | _ -> false in
  let found_lend = ref false and found_alias = ref false in
  Core_walk.walk_expression
    {
      Core_walk.ignore_all with
      place = (fun place -> if is_lent place then found_lend := true);
      pattern = (fun pattern -> if may_alias pattern then found_alias := true);
    }
    condition;
  !found_lend && !found_alias

let is_executable state (condition : Core.expression) =
  let executable = ref true in
  let is_specification_only (callee : Core.callee) =
    match callee.target with
    | Function { path; _ } -> (
        match Instantiation.find_function_signature state path with
        | Some signature -> signature.specification_only
        | _ -> false)
    | Trait_method { trait; name; receiver; _ } ->
        List.exists
          (fun (method_ : Types.trait_method) ->
            method_.method_receiver = receiver
            && (Members.read_method_signature state.lookups trait.trait method_).specification_only)
          (Members.list_trait_methods state.lookups trait.trait name)
    | Capability_method _ | Intrinsic _ | Indirect _ -> false
  in
  Core_walk.walk_expression
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          if node.type_ = Types.Integer then executable := false;
          match node.kind with
          | Quantified { binder = Over_type _; _ }
          | Result | Old _ | Yielded | Identical _ | Specification_function _ | Method_cost _
          | Convert { conversion = To_integer | From_integer; _ } ->
              executable := false
          | _ -> ());
      callee = (fun callee -> if is_specification_only callee then executable := false);
    }
    condition;
  !executable

let build_compound_assign state (written : Syntax.statement) (target : Syntax.expression)
    (value : Syntax.expression) operation : Core.statement_kind =
  let place = State.make_place (State.build_expression state target) in
  let target_type = read_type state target in
  let current =
    State.make_synthetic_expression state ~origin:written.id target_type Core.Current_target
  in
  let right = State.build_expression state value in
  let bound = State.allocate_synthetic_local state in
  let bound_value =
    State.make_synthetic_expression state ~origin:value.id right.type_
      (Use (Local { local = bound; type_ = right.type_; origin = value.id }))
  in
  let make_built_in operation : Core.kind * Core.operand =
    (Operator { operation; arguments = [ current; bound_value ] }, Operands.build Own right)
  in
  let kind, right_operand =
    match state.tables.calls.(written.id) with
    | Some ({ callee = Trait_method { trait; name; receiver; self_type; _ }; _ } as recorded) -> (
        match find_built_in_operation trait name receiver self_type with
        | Some operation -> make_built_in operation
        | None ->
            let read_argument_mode index =
              match
                List.find_opt
                  (fun (argument : Tables.argument) -> argument.core_argument_index = index)
                  recorded.arguments
              with
              | Some argument -> argument.mode
              | None -> Language.Mode.Read
            in
            ( Call
                (State.make_call state
                   ~callee:(convert_callee state recorded.callee)
                   ~arguments:
                     [
                       Operands.build_argument (read_argument_mode 0) current;
                       Operands.build_argument (read_argument_mode 1) bound_value;
                     ]
                   ~lends:None),
              Operands.build
                (State.decide_binding_mode state (read_argument_mode 1) right.type_)
                right ))
    | Some _ -> State.raise_bug "a compound assignment's call is not a trait method call"
    | None -> make_built_in (convert_to_operation operation)
  in
  Compound_assign
    {
      target = place;
      operand = right_operand;
      bound;
      value = State.make_synthetic_expression state ~origin:written.id target_type kind;
    }

let rec lend_statements state (mode : Language.Mode.t) (value : Core.expression) :
    Core.statement list =
  let make_statement kind : Core.statement list =
    [ { id = State.allocate_node_id state; origin = value.origin; kind } ]
  in
  let make_branching kind =
    let type_ = if value.type_ = Types.Never then Types.Never else Types.unit in
    make_statement (Evaluate { value with type_; kind })
  in
  match value.kind with
  | If { condition; then_; else_ = Some else_; binds_lent_part } ->
      make_branching
        (If
           {
             condition;
             then_ = lend_block state mode then_;
             else_ = Some (lend_block state mode else_);
             binds_lent_part;
           })
  | Match { scrutinees; arms } ->
      make_branching
        (Match
           {
             scrutinees;
             arms =
               List.map
                 (fun (arm : Core.arm) -> { arm with body = lend_block state mode arm.body })
                 arms;
           })
  | Block body -> make_branching (Block (lend_block state mode body))
  | _ when value.type_ = Types.Never -> make_statement (Evaluate value)
  | _ -> make_statement (Yield { mode; part = Operands.build mode value })

and lend_block state mode (body : Core.block) : Core.block =
  match body.value with
  | None -> body
  | Some value -> { statements = body.statements @ lend_statements state mode value; value = None }

let rec is_fixed_place : Core.place -> bool = function
  | Local _ | Constant _ -> true
  | Field { base; _ } -> is_fixed_place base
  | Lent _ | Temporary _ -> false

let build_collection_place state (iterable : Syntax.expression) (mode : Language.Mode.t) :
    Core.place * (type_:Types.ty -> Core.block -> Core.kind) option =
  let collection = State.build_expression state iterable in
  match collection.kind with
  | Use place when is_fixed_place place -> (place, None)
  | _ ->
      let local = State.allocate_synthetic_local state and origin = iterable.id in
      let scrutinee = Operands.build mode collection in
      let pattern : Core.pattern =
        {
          id = State.allocate_node_id state;
          origin;
          type_ = collection.type_;
          kind =
            Bind
              {
                local;
                is_var = false;
                mode = (match scrutinee with Place _ -> mode | Value _ -> Own);
              };
        }
      in
      ( Local { local; type_ = collection.type_; origin },
        Some
          (fun ~type_:_ body ->
            Match
              {
                scrutinees = [ scrutinee ];
                arms = [ { patterns = [ pattern ]; guard = None; body; origin } ];
              }) )

let build_elements state ~origin (collection : Core.place) ~(count : Tables.call)
    ~(element : Tables.call) ~(lends : Language.Mode.t) : Core.elements =
  let uint64 = Types.make_builtin UInt64 in
  let local = State.allocate_synthetic_local state in
  let make_receiver mode : Core.argument = Passed { mode; value = Place collection } in
  let position =
    State.make_synthetic_expression state ~origin uint64
      (Use (Local { local; type_ = uint64; origin }))
  in
  {
    count =
      State.make_synthetic_expression state ~origin uint64
        (Call
           (State.make_call state
              ~callee:(convert_callee state count.callee)
              ~arguments:[ make_receiver Read ]
              ~lends:None));
    position =
      {
        id = State.allocate_node_id state;
        origin;
        type_ = uint64;
        kind = Bind { local; is_var = false; mode = Own };
      };
    element =
      Lent
        (State.make_synthetic_expression state ~origin element.callee_result
           (Call
              (State.make_call state
                 ~callee:(convert_callee state element.callee)
                 ~arguments:
                   [
                     make_receiver lends;
                     Passed { mode = Read; value = Operands.build Read position };
                   ]
                 ~lends:(Some lends))));
  }

let quantify_over_elements state (collection : Syntax.expression) ~count ~element ~lends ~origin
    make_quantified : Core.kind =
  let place, wrap = build_collection_place state collection lends in
  let kind =
    make_quantified (build_elements state ~origin:collection.id place ~count ~element ~lends)
  in
  match wrap with
  | None -> kind
  | Some wrap ->
      wrap ~type_:Types.bool
        {
          statements = [];
          value = Some (State.make_synthetic_expression state ~origin Types.bool kind);
        }

let build_cursor_next state (cursor : Types.ty) : Core.callee =
  let { Well_known.owner; name; receiver } = Well_known.locate_method Cursor_next in
  let trait = State.make_trait_reference ~arguments:[] (Well_known.make_path owner) in
  State.make_callee state
    (Trait_method
       {
         trait;
         name;
         receiver;
         self_type = cursor;
         instantiation = Types.no_instantiation;
         evidence = read_evidence state cursor trait;
       })

let build_for_loop (state : State.state) (written : Syntax.statement) (iterable : Syntax.expression)
    ~pattern ~clauses ~body ~mode : Core.statement_kind =
  let make_loop iteration : Core.statement_kind = For { pattern; iteration; clauses; body; mode } in
  match (state.tables.loops.(written.id), iterable.kind) with
  | Some (Integer_range { inclusive; _ }), Range { start = Some start; stop = Some stop; _ } ->
      let start = State.build_expression state start in
      make_loop (Integer_range { start; stop = State.build_expression state stop; inclusive })
  | Some (Elements { count; element; lends }), _ -> (
      let place, wrap = build_collection_place state iterable lends in
      let elements_loop =
        make_loop (Elements (build_elements state ~origin:iterable.id place ~count ~element ~lends))
      in
      match wrap with
      | None -> elements_loop
      | Some wrap ->
          let statement : Core.statement =
            { id = State.allocate_node_id state; origin = written.id; kind = elements_loop }
          in
          Evaluate
            (State.make_synthetic_expression state ~origin:written.id Types.unit
               (wrap ~type_:Types.unit { statements = [ statement ]; value = None })))
  | Some (Pulled { cursor; cursor_call; remaining }), _ -> (
      let collection = State.build_expression state iterable in
      let pulled =
        match cursor_call with
        | None -> collection
        | Some cursor_call ->
            State.make_synthetic_expression state ~origin:iterable.id cursor
              (Call
                 (State.make_call state
                    ~callee:(convert_callee state cursor_call.callee)
                    ~arguments:[ Passed { mode = Own; value = Operands.build Own collection } ]
                    ~lends:None))
      in
      let next = build_cursor_next state cursor in
      let make_cursor_loop ?remaining (place : Core.place) : Core.statement_kind =
        let measure =
          Option.map
            (fun (remaining : Tables.call) ->
              Core.Decreases
                [
                  State.make_synthetic_expression state ~origin:iterable.id
                    (Types.make_builtin UInt64)
                    (Call
                       (State.make_call state
                          ~callee:(convert_callee state remaining.callee)
                          ~arguments:[ Passed { mode = Read; value = Place place } ]
                          ~lends:None));
                ])
            remaining
        in
        For
          {
            pattern;
            iteration = Cursor { cursor = place; next };
            clauses = clauses @ Option.to_list measure;
            body;
            mode;
          }
      in
      match (pulled.kind, if Core_walk.states_measure clauses then None else remaining) with
      | Use place, remaining when is_fixed_place place -> make_cursor_loop ?remaining place
      | _, None -> make_cursor_loop (State.make_place pulled)
      | _, Some remaining ->
          let local = State.allocate_synthetic_local state and origin = iterable.id in
          let binding : Core.pattern =
            {
              id = State.allocate_node_id state;
              origin;
              type_ = pulled.type_;
              kind = Bind { local; is_var = true; mode = Own };
            }
          in
          let statement : Core.statement =
            {
              id = State.allocate_node_id state;
              origin = written.id;
              kind = make_cursor_loop ~remaining (Local { local; type_ = pulled.type_; origin });
            }
          in
          Evaluate
            (State.make_synthetic_expression state ~origin:written.id Types.unit
               (Match
                  {
                    scrutinees = [ Operands.build Own pulled ];
                    arms =
                      [
                        {
                          patterns = [ binding ];
                          guard = None;
                          body = { statements = [ statement ]; value = None };
                          origin;
                        };
                      ];
                  })))
  | _ -> State.raise_bug "the checker recorded no iteration for a `for` loop"

let convert_resource state (written : Syntax.resource) : Core.resource =
  let resolve_capability (path : Syntax.path_type) =
    match State.find_target state path.path.last with
    | Some (Definition (Capability, capability)) -> capability
    | _ -> State.raise_bug "`calls` names something that is not a capability"
  in
  match written with
  | Metric metric -> Metric metric
  | Calls (Call_parameter name) -> (
      match State.find_target state name with
      | Some (Local id) -> Calls (Function_parameter (build_declared_local state id))
      | _ -> State.raise_bug "`calls(%s)` names no parameter" name.text)
  | Calls (Call_capability path) -> Calls (Capability (resolve_capability path))
  | Calls (Call_method (path, method_)) ->
      Calls (Capability_method (resolve_capability path, method_.text))

let build_cost state ~origin ({ amortized; resource = written; bound } : Syntax.cost) : Core.cost =
  {
    origin;
    amortized;
    resource = convert_resource state written;
    bound =
      (match bound with
      | Big_o value -> Order_of (State.build_expression state value)
      | At_most value -> At_most (State.build_expression state value)
      | Exactly value -> Exactly (State.build_expression state value));
  }

let build_loop_clause state (clause : Syntax.loop_clause) : Core.loop_clause =
  match clause.kind with
  | Invariant value -> Invariant (State.build_expression state value)
  | Loop_decreases measures -> Decreases (List.map (State.build_expression state) measures)
  | Loop_cost written -> Cost (build_cost state ~origin:clause.id written)

let build_try state (value : Syntax.expression) (inner : Syntax.expression) ~(output : Types.ty) :
    Core.kind =
  let scrutinee = State.build_expression state inner in
  let read_variants (type_ : Types.ty) =
    match type_ with
    | Types.Named { path; arguments } -> (
        match Members.find_variants state.lookups path arguments with
        | Some [ success; failure ] -> (success, failure)
        | _ -> State.raise_bug "`?` on `%s`" (Types.show type_))
    | _ -> State.raise_bug "`?` on `%s`" (Types.show type_)
  in
  let success, failure = read_variants scrutinee.type_ in
  let _, returned_failure = read_variants output in
  let make = State.make_synthetic_expression state ~origin:value.id in
  let bind_fields (variant : Types.variant) : Core.pattern * (string * Core.expression) list =
    let fields =
      List.map
        (fun (field : Types.field) -> (field, State.allocate_synthetic_local state))
        (Option.value ~default:[] variant.fields)
    in
    ( {
        id = State.allocate_node_id state;
        origin = value.id;
        type_ = scrutinee.type_;
        kind =
          Variant
            {
              variant = variant.variant_name;
              fields =
                List.map
                  (fun ((field : Types.field), local) : (string * Core.pattern) ->
                    ( field.field_name,
                      {
                        id = State.allocate_node_id state;
                        origin = value.id;
                        type_ = field.field_type;
                        kind = Bind { local; is_var = false; mode = Own };
                      } ))
                  fields;
            };
      },
      List.map
        (fun ((field : Types.field), local) ->
          ( field.field_name,
            make field.field_type
              (Core.Use (Local { local; type_ = field.field_type; origin = value.id })) ))
        fields )
  in
  let success_pattern, success_fields = bind_fields success in
  let failure_pattern, failure_fields = bind_fields failure in
  let make_arm patterns body : Core.arm = { patterns; guard = None; body; origin = value.id } in
  Match
    {
      scrutinees = [ Operands.build Own scrutinee ];
      arms =
        [
          make_arm [ success_pattern ]
            {
              statements = [];
              value = (match success_fields with [ (_, field) ] -> Some field | _ -> None);
            };
          make_arm [ failure_pattern ]
            {
              statements = [];
              value =
                Some
                  (make Types.Never
                     (Return
                        (Some
                           (make output
                              (Construct
                                 {
                                   variant = Some returned_failure.variant_name;
                                   fields =
                                     List.map2
                                       (fun (field : Types.field) (_, field_value) ->
                                         (field.field_name, Some (Operands.build Own field_value)))
                                       (Option.value ~default:[] returned_failure.fields)
                                       failure_fields;
                                 })))));
            };
        ];
    }

let build_collection_literal state (value : Syntax.expression) (elements : Core.expression list) :
    Core.kind =
  match read_type state value with
  | Types.Named { path; arguments = [ Types.Type element ] } when Well_known.is List path ->
      build_list_literal state ~origin:value.id element elements
  | Types.Named { path; _ } when Intrinsic.find_builtin path = Some Array ->
      Collection_literal { elements; construction = Array }
  | Types.Named { path; _ } when Well_known.is Sequence path || Well_known.is Finite_set path ->
      Collection_literal { elements; construction = Specification_only }
  | type_ -> State.raise_bug "a collection literal of type `%s`" (Types.show type_)

let build_converted_literal state (value : Syntax.expression) ~(element : Types.ty)
    (elements : Core.expression list) : Core.kind =
  let recorded = read_call state value.id in
  let list =
    State.make_synthetic_expression state ~origin:value.id
      (Types.make_named (Well_known.make_path List) [ element ])
      (build_list_literal state ~origin:value.id element elements)
  in
  Call
    (State.make_call state
       ~callee:(convert_callee state recorded.callee)
       ~arguments:[ Operands.build_argument Own list ]
       ~lends:None)

let build_converted_map_literal state (value : Syntax.expression) ~(key : Types.ty)
    ~(value_type : Types.ty) (entries : (Core.expression * Core.expression) list) : Core.kind =
  let entry = Types.make_named (Well_known.make_path Entry) [ key; value_type ] in
  build_converted_literal state value ~element:entry
    (List.map
       (fun (entry_key, entry_value) ->
         State.make_synthetic_expression state ~origin:value.id entry
           (build_record [ (Entry_key, entry_key); (Entry_value, entry_value) ]))
       entries)

open Syntax
module Impls = Interface.Impls
module Properties = Interface.Properties
open State
open Instantiation

let build_expression_by_id state (id : id) : Core.expression =
  match state.form.expression_builders.(id) with
  | Some build -> build ()
  | None -> bug "a call's argument has no core node"

let read_call state (id : id) : Tables.call =
  match state.tables.calls.(id) with
  | Some call -> call
  | None -> bug "the checker recorded no call for a call node"

let convert_evidence : Tables.evidence -> Core.evidence = function
  | Impl { impl; arguments } -> Impl { impl; arguments }
  | Bound -> Bound
  | Dynamic -> Dynamic
  | Built_in -> bug "a built-in method has no core evidence"

let convert_callee (callee : Tables.callee) : Core.callee =
  match callee with
  | Function { path; type_arguments } -> Function { path; type_arguments }
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence = inferred } ->
      Trait_method
        { trait; name; receiver; self_type; type_arguments; evidence = convert_evidence inferred }
  | Capability_method { capability; name } -> Capability_method { capability; name }
  | Intrinsic { operation; type_arguments } -> Intrinsic { operation; type_arguments }
  | Constructor _ | Indirect | Built_in_operator -> bug "this callee has no core callee"

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
              value = build_operand argument.mode (build_expression_by_id state argument.expression);
              mode_keyword = argument.mode_keyword;
            }
      | None -> Default)

let build_call state ~lends ?function_value (call : Tables.call) : Core.call =
  {
    callee =
      (match (call.callee, function_value) with
      | Indirect, Some function_value -> Indirect (build_operand Read function_value)
      | direct, _ -> convert_callee direct);
    arguments = build_arguments state call;
    lends;
    uses = call.uses;
  }

let arithmetic_traits : (Well_known.t * string * Intrinsic.operation) list =
  [
    (Add, "add", Add);
    (Subtract, "subtract", Subtract);
    (Multiply, "multiply", Multiply);
    (Divide, "divide", Divide);
    (Remainder, "remainder", Remainder);
    (Negate, "negate", Negate);
  ]

let is_number type_ = Types.is_integer_type type_ || Types.is_float_type type_

let is_built_in_scalar type_ =
  is_number type_ || Types.is_builtin Bool type_ || Types.is_builtin Character type_

let find_built_in_operation (trait : Types.trait_reference) name self_type =
  if
    is_number self_type
    && List.for_all (fun argument -> argument = Types.Type self_type) trait.trait_arguments
  then
    List.find_map
      (fun (known, method_, operation) ->
        if method_ = name && Well_known.is known trait.trait then Some operation else None)
      arithmetic_traits
  else None

let build_argument_expressions state (call : Tables.call) =
  List.map
    (fun (argument : Tables.argument) -> build_expression_by_id state argument.expression)
    (List.sort
       (fun (left : Tables.argument) (right : Tables.argument) ->
         compare left.core_argument_index right.core_argument_index)
       call.arguments)

let read_constructor_fields state type_ variant type_arguments =
  let fields =
    match variant with
    | None -> Members.fields state.lookups type_ type_arguments
    | Some variant ->
        Option.bind (Members.variants state.lookups type_ type_arguments) (fun variants ->
            Option.bind
              (List.find_opt
                 (fun (written : Types.variant) -> written.variant_name = variant)
                 variants)
              (fun (written : Types.variant) -> written.fields))
  in
  match fields with
  | Some fields -> fields
  | None -> bug "`%s` is constructed but has no fields" (Path.show type_)

let build_call_kind ?lends ?function_value state (value : expression) : Core.kind =
  let recorded = read_call state value.id in
  let lends =
    match lends with Some lends -> Some lends | None -> state.tables.lend_modes.(value.id)
  in
  match recorded.callee with
  | Trait_method { trait; evidence = Built_in; _ }
    when Path.equal trait.trait Properties.copyable_trait -> (
      match recorded.arguments with
      | [ receiver ] -> Copy (build_operand Read (build_expression_by_id state receiver.expression))
      | _ -> bug "`copy` does not have exactly one argument")
  | Trait_method { trait; name; self_type; _ }
    when Option.is_some (find_built_in_operation trait name self_type) ->
      Operator
        {
          operation = Option.get (find_built_in_operation trait name self_type);
          arguments = build_argument_expressions state recorded;
        }
  | Trait_method { trait; name = "equal"; self_type; _ }
    when is_built_in_scalar self_type && Well_known.is Equal trait.trait -> (
      match build_argument_expressions state recorded with
      | [ left; right ] -> Compare { comparison = Equal; left; right }
      | _ -> bug "`equal` does not have exactly two arguments")
  | Constructor { type_; variant; type_arguments } ->
      let declared = read_constructor_fields state type_ variant type_arguments in
      let written =
        List.map
          (fun (argument : Tables.argument) ->
            ( (List.nth declared argument.core_argument_index).field_name,
              Some (build_operand argument.mode (build_expression_by_id state argument.expression))
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
  | Built_in_operator -> bug "an operator is recorded as a call"
  | Indirect | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> (
      let function_value = Option.map (build_expression state) function_value in
      let call = Core.Call (build_call state ~lends ?function_value recorded) in
      match lends with
      | Some _ ->
          Use (Lent (synthetic_expression state ~origin:value.id recorded.callee_result call))
      | None -> call)

let register_call ?function_value state (value : expression) =
  register_expression state value (fun () -> build_call_kind ?function_value state value)

let register_index state (value : expression) =
  register_expression state value (fun () ->
      match (read_call state value.id).callee with
      | Trait_method { receiver = Mut; _ } -> build_call_kind ~lends:Mut state value
      | _ -> build_call_kind ~lends:Read state value)

let build_numeric_literal state (id : id) : Core.kind =
  match state.tables.literals.(id) with
  | Some (Integer_value number) -> Integer number
  | Some (Float_value number) -> Float number
  | None -> bug "a literal has no value"

let read_type state (value : expression) =
  match state.tables.types.(value.id) with
  | Some type_ -> type_
  | None ->
      bug "`%s` has a core node but no recorded type" (source state (read_span state value.id))

let build_function_value state (value : expression) : Core.kind =
  match state.tables.resolutions.(value.id) with
  | Some (Global { path; type_arguments }) -> Function_value { path; type_arguments }
  | _ -> bug "`%s` is not recorded as a function" (source state (read_span state value.id))

let build_variant_value state (value : expression) type_path variant : Core.kind =
  match read_type state value with
  | Types.Function { output = Types.Named { arguments; _ } as variant_type; _ } ->
      let fields =
        List.map
          (fun (field : Types.field) -> (field, fresh_synthetic_local state))
          (read_constructor_fields state type_path (Some variant) arguments)
      in
      Lambda
        {
          parameters =
            List.map
              (fun ((field : Types.field), local) : Core.pattern ->
                {
                  id = fresh_node_id state;
                  origin = value.id;
                  type_ = field.field_type;
                  kind = Bind { local; name = field.field_name; is_var = false; mode = Own };
                })
              fields;
          captures = [];
          body =
            {
              statements = [];
              value =
                Some
                  (synthetic_expression state ~origin:value.id variant_type
                     (Construct
                        {
                          variant = Some variant;
                          fields =
                            List.map
                              (fun ((field : Types.field), local) ->
                                ( field.field_name,
                                  Some
                                    (Core.Value
                                       (synthetic_expression state ~origin:value.id field.field_type
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

let read_local_type state (id : id) =
  match state.tables.local_types.(id) with
  | Some type_ -> type_
  | None -> bug "a local has no recorded type"

let build_named_local state ~origin (id : id) : Core.place =
  Local { local = Named id; type_ = read_local_type state id; origin }

let build_local_use state ~origin (id : id) : Core.kind =
  if was_hole state (fun tables -> tables.local_types) id then Todo
  else Use (build_named_local state ~origin id)

let read_self_type state (env : env) =
  match env.self with
  | Some type_ -> final_type state type_
  | None -> bug "`self` is used outside a method"

let build_self_local state (env : env) ~origin : Core.place =
  Local { local = Self; type_ = read_self_type state env; origin }

let build_constant_place state ~origin (path : Path.t) : Core.place =
  match Interface.Definition.constant_type state.lookups.interface path with
  | Some type_ -> Constant { path; type_; origin }
  | None -> bug "the constant `%s` has no type" (Path.show path)

let build_record fields : Core.kind =
  Construct
    {
      variant = None;
      fields = List.map (fun (name, value) -> (name, Some (Core.Value value))) fields;
    }

let build_range_record state (value : expression) start stop ~inclusive : Core.kind =
  match (start, stop) with
  | Some start, Some stop ->
      let start = build_expression state start in
      let stop = build_expression state stop in
      let inclusive =
        synthetic_expression state ~origin:value.id Types.bool (Core.Boolean inclusive)
      in
      build_record [ ("start", start); ("stop", stop); ("inclusive", inclusive) ]
  | _ -> bug "a range without both bounds is valid only inside a slice"

let find_capability_impls (state : state) (type_ : Types.ty) =
  match type_ with
  | Types.Named { path; _ } ->
      List.filter_map
        (fun (trait, _) ->
          if Resolve.Names.kind_of state.lookups.interface.names trait = Some Capability then
            match implements state type_ (trait_reference trait) with
            | Some (Interface.Impls.From_impl { impl; substitution }) ->
                Option.map
                  (fun interface ->
                    ({ Core.capability = trait; impl; arguments = substitution }, interface))
                  (Interface.Impls.impl_interface state.lookups.interface impl)
            | _ -> None
          else None)
        (List.concat_map
           (fun package -> Interface.Impls.impls_for state.lookups.interface path package)
           (List.sort_uniq compare [ Path.package path; state.package; Path.standard_package ]))
  | _ -> []

let build_provide state (implementations : expression list) (body : block) : Core.kind =
  let implementations =
    List.map
      (fun (implementation : expression) : Core.implementation ->
        let mode : Types.mode = match implementation.kind with Mode (Mut, _) -> Mut | _ -> Read in
        let node = build_expression state implementation in
        {
          origin = implementation.id;
          mode;
          value = build_operand mode node;
          type_ = node.type_;
          provides = List.map fst (find_capability_impls state node.type_);
        })
      implementations
  in
  Provide { implementations; body = build_block state body }

let build_text_builder_callee name receiver : Core.callee =
  Function
    { path = Method { owner = Well_known.path Text_builder; name; receiver }; type_arguments = [] }

let read_template state (literal : string_literal) =
  match state.tables.templates.(literal.id) with
  | Some template -> template
  | None -> bug "the checker recorded no template for a string literal"

let build_untagged_string state ~origin (literal : string_literal) : Core.kind =
  match literal.rest with
  | [] -> String literal.first.value
  | rest ->
      let make = synthetic_expression state ~origin in
      let make_statement kind : Core.statement = { id = fresh_node_id state; origin; kind } in
      let builder_type = Types.named (Well_known.path Text_builder) [] in
      let builder = fresh_synthetic_local state in
      let builder_place : Core.place = Local { local = builder; type_ = builder_type; origin } in
      let make_call callee arguments : Core.kind =
        Call { callee; arguments; lends = None; uses = Types.no_capabilities }
      in
      let let_builder =
        make_statement
          (Let
             {
               pattern =
                 {
                   id = fresh_node_id state;
                   origin;
                   type_ = builder_type;
                   kind = Bind { local = builder; name = "builder"; is_var = true; mode = Own };
                 };
               value =
                 Value (make builder_type (make_call (build_text_builder_callee "new" Static) []));
               else_ = None;
             })
      in
      let write (written : Syntax.text) =
        if written.value = "" then []
        else
          [
            make_statement
              (Evaluate
                 (make Types.unit
                    (make_call
                       (build_text_builder_callee "write" Mut)
                       [
                         Passed { mode = Mut; value = Place builder_place; mode_keyword = None };
                         Passed
                           {
                             mode = Read;
                             value =
                               Value
                                 (make
                                    (Types.named (Well_known.path String_slice) [])
                                    (String written.value));
                             mode_keyword = None;
                           };
                       ])));
          ]
      in
      let display part (conversion : Tables.call option) =
        match conversion with
        | Some recorded ->
            make_statement
              (Evaluate
                 (make Types.unit
                    (Call
                       {
                         callee = convert_callee recorded.callee;
                         arguments =
                           [
                             Passed
                               {
                                 mode = Read;
                                 value = build_operand Read (build_expression state part);
                                 mode_keyword = None;
                               };
                             Passed { mode = Mut; value = Place builder_place; mode_keyword = None };
                           ];
                         lends = None;
                         uses = recorded.uses;
                       })))
        | None -> bug "an interpolated value has no `display`"
      in
      Block
        {
          statements =
            (let_builder :: write literal.first)
            @ List.concat
                (List.map2
                   (fun (part, after) conversion -> display part conversion :: write after)
                   rest (read_template state literal).part_conversions);
          value =
            Some
              (make string_type
                 (make_call
                    (build_text_builder_callee "finish" Own)
                    [
                      Passed
                        {
                          mode = Own;
                          value = Value (make builder_type (Use builder_place));
                          mode_keyword = None;
                        };
                    ]));
        }

let build_list_literal state ~origin (element : Types.ty) (elements : Core.expression list) :
    Core.kind =
  let make = synthetic_expression state ~origin in
  let make_statement kind : Core.statement = { id = fresh_node_id state; origin; kind } in
  let storage_type =
    Types.Named { path = Intrinsic.builtin_path Storage; arguments = [ Types.Type element ] }
  in
  let storage = fresh_synthetic_local state in
  let make_intrinsic_call operation type_ arguments =
    make type_
      (Call
         {
           callee = Intrinsic { operation; type_arguments = [ Types.Type element ] };
           arguments;
           lends = None;
           uses = Types.no_capabilities;
         })
  in
  let capacity = make (Types.builtin UInt64) (Integer (Z.of_int (List.length elements))) in
  let let_storage =
    make_statement
      (Let
         {
           pattern =
             {
               id = fresh_node_id state;
               origin;
               type_ = storage_type;
               kind = Bind { local = storage; name = "storage"; is_var = true; mode = Own };
             };
           value =
             Value
               (make_intrinsic_call Storage_with_capacity storage_type
                  [ Passed { mode = Read; value = Value capacity; mode_keyword = None } ]);
           else_ = None;
         })
  in
  let pushes =
    List.map
      (fun element ->
        make_statement
          (Evaluate
             (make_intrinsic_call Storage_push Types.unit
                [
                  Passed
                    {
                      mode = Mut;
                      value = Place (Local { local = storage; type_ = storage_type; origin });
                      mode_keyword = None;
                    };
                  Passed { mode = Own; value = Value element; mode_keyword = None };
                ])))
      elements
  in
  Block
    {
      statements = let_storage :: pushes;
      value =
        Some
          (make
             (Types.named (Well_known.path List) [ element ])
             (Call
                {
                  callee =
                    Function
                      {
                        path =
                          Method
                            {
                              owner = Well_known.path List;
                              name = "from_storage";
                              receiver = Static;
                            };
                        type_arguments = [ Types.Type element ];
                      };
                  arguments =
                    [
                      Passed
                        {
                          mode = Own;
                          value =
                            Value
                              (make storage_type
                                 (Use (Local { local = storage; type_ = storage_type; origin })));
                          mode_keyword = None;
                        };
                    ];
                  lends = None;
                  uses = Types.no_capabilities;
                }));
    }

let build_tagged_string state (value : expression) (literal : string_literal) ~(part : Types.ty) :
    Core.kind =
  let recorded = read_template state literal in
  let from_template =
    match recorded.from_template with
    | Some call -> call
    | None -> bug "a tagged string has no `from_template`"
  in
  let make = synthetic_expression state ~origin:value.id in
  let make_list element elements =
    make
      (Types.named (Well_known.path List) [ element ])
      (build_list_literal state ~origin:value.id element elements)
  in
  let literal_type = Types.named (Well_known.path Literal) [] in
  let texts =
    List.map
      (fun (written : Syntax.text) ->
        make literal_type
          (build_record
             [
               ("text", make (Types.named (Well_known.path String_slice) []) (String written.value));
             ]))
      (literal.first :: List.map snd literal.rest)
  in
  let parts =
    List.map2
      (fun ((written : expression), _) (conversion : Tables.call option) ->
        match conversion with
        | Some call ->
            synthetic_expression state ~origin:written.id call.callee_result
              (Call (build_call state ~lends:None call))
        | None -> build_expression state written)
      literal.rest recorded.part_conversions
  in
  let texts = make_list literal_type texts in
  let template =
    make
      (Types.named (Well_known.path Template) [ part ])
      (build_record [ ("literals", texts); ("parts", make_list part parts) ])
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
             {
               callee = convert_callee from_template.callee;
               arguments = [ Passed { mode = Read; value = Value template; mode_keyword = None } ];
               lends = None;
               uses = from_template.uses;
             });
    }

let read_pattern_type state (id : id) =
  match state.tables.scrutinee_types.(id) with
  | Some type_ -> type_
  | None -> bug "a pattern has no recorded type"

let build_constant_pattern state (id : id) (value : Core.pattern_constant) : Core.pattern_kind =
  let type_ = read_pattern_type state id in
  if is_built_in_scalar type_ then Literal value
  else
    let equal = trait_reference (Well_known.path Equal) in
    match implements state type_ equal with
    | Some implementation ->
        Equal_to
          {
            value;
            equal =
              Trait_method
                {
                  trait = equal;
                  name = "equal";
                  receiver = Read;
                  self_type = type_;
                  type_arguments = [];
                  evidence = convert_evidence (evidence_of implementation);
                };
          }
    | None ->
        bug "a pattern compares values of `%s`, which does not implement `Equal`" (Types.show type_)

let read_constant_path state (id : id) =
  match state.tables.patterns.(id) with
  | Some (Constant_pattern path) -> path
  | _ -> bug "a pattern names a constant that was not recorded"

let build_named_constant state (id : id) : Core.pattern_constant =
  Named_constant (read_constant_path state id)

let build_literal_constant state (id : id) (written : Syntax.literal) : Core.pattern_constant =
  match (written, state.tables.literals.(id)) with
  | _, Some (Integer_value number) -> Integer_constant number
  | Literal_true, _ -> Boolean_constant true
  | Literal_false, _ -> Boolean_constant false
  | Literal_string text, _ -> String_constant text.first.value
  | Literal_integer _, _ -> bug "an integer pattern has no value"

let build_range_bound state (bound : Syntax.range_end) : Core.range_bound =
  match bound.kind with
  | End_literal _ -> (
      match state.tables.literals.(bound.id) with
      | Some (Integer_value number) -> Integer_bound number
      | Some (Float_value _) | None -> bug "a range bound has no integer value")
  | End_constant _ -> Constant_bound (read_constant_path state bound.id)

let build_pattern_fields state (fields : Types.field list) (matched : (string * pattern) list) =
  List.filter_map
    (fun (field : Types.field) ->
      Option.map
        (fun written -> (field.field_name, build_pattern state written))
        (List.assoc_opt field.field_name matched))
    fields

let convert_to_integer state (node : Core.expression) : Core.expression =
  if node.type_ = Types.Integer || not (integer_type state node.type_) then node
  else
    synthetic_expression state ~origin:node.origin Types.Integer
      (Convert { conversion = To_integer; value = node })

let convert_to_operation : Syntax.operation -> Intrinsic.operation = function
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

let build_operator state (value : expression) operation (operands : expression list) : Core.kind =
  let arguments = List.map (build_expression state) operands in
  Operator
    {
      operation;
      arguments =
        (if read_type state value = Types.Integer then List.map (convert_to_integer state) arguments
         else arguments);
    }

let convert_to_comparison : Syntax.comparison -> Core.comparison = function
  | Equal -> Equal
  | Not_equal -> Not_equal
  | Less -> Less
  | Less_equal -> Less_equal
  | Greater -> Greater
  | Greater_equal -> Greater_equal

let build_built_in_comparison state comparison (left : expression) (right : expression) : Core.kind
    =
  let left = build_expression state left in
  let right = build_expression state right in
  let left, right =
    if Types.equal left.type_ right.type_ then (left, right)
    else (convert_to_integer state left, convert_to_integer state right)
  in
  Compare { comparison = convert_to_comparison comparison; left; right }

let build_comparison state (value : expression) comparison (left : expression) (right : expression)
    : Core.kind =
  let recorded = read_call state value.id in
  match recorded.callee with
  | Trait_method { self_type; _ } when is_built_in_scalar self_type ->
      build_built_in_comparison state comparison left right
  | _ -> (
      let call =
        synthetic_expression state ~origin:value.id recorded.callee_result
          (Call (build_call state ~lends:None recorded))
      in
      let make_matches_variant variant : Core.kind =
        Matches
          {
            value = Value call;
            pattern =
              {
                id = fresh_node_id state;
                origin = value.id;
                type_ = recorded.callee_result;
                kind = Variant { variant; fields = [] };
              };
          }
      in
      let make_not kind : Core.kind =
        Not (synthetic_expression state ~origin:value.id Types.bool kind)
      in
      match comparison with
      | Equal -> call.kind
      | Not_equal -> Not call
      | Less -> make_matches_variant "Less"
      | Less_equal -> make_not (make_matches_variant "Greater")
      | Greater -> make_matches_variant "Greater"
      | Greater_equal -> make_not (make_matches_variant "Less"))

let binds_lent_part state (condition : Core.expression) =
  let may_alias (pattern : Core.pattern) =
    match pattern.kind with
    | Bind { mode = Mut; _ } -> true
    | Bind { mode = Read | Own; _ } ->
        State.is_view state pattern.type_ || not (State.plain state pattern.type_)
    | Wildcard | Variant _ | Record _ | Alternatives _ | Literal _ | Range _ | Equal_to _ -> false
  in
  let is_lent (place : Core.place) = match place with Lent _ -> true | _ -> false in
  let found_lend = ref false and found_alias = ref false in
  Core_walk.expression
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
    match callee with
    | Function { path; _ } -> (
        match function_signature state path with
        | Some signature -> signature.specification_only
        | _ -> false)
    | Trait_method { trait; name; receiver; _ } ->
        List.exists
          (fun (method_ : Types.trait_method) ->
            method_.method_receiver = receiver
            && (Members.method_signature state.lookups trait.trait method_).specification_only)
          (Members.trait_methods state.lookups trait.trait name)
    | Capability_method _ | Intrinsic _ | Indirect _ -> false
  in
  Core_walk.expression
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          if node.type_ = Types.Integer then executable := false;
          match node.kind with
          | Quantified _ | Result | Old _ | Yielded | Identical _ | Specification_function _
          | Method_time _
          | Convert { conversion = To_integer | From_integer; _ } ->
              executable := false
          | Call { callee; _ } -> if is_specification_only callee then executable := false
          | _ -> ());
    }
    condition;
  !executable

let build_compound_assign state (written : statement) (target : expression) (value : expression)
    operation : Core.statement_kind =
  let place = place_of (build_expression state target) in
  let target_type = read_type state target in
  let current = synthetic_expression state ~origin:written.id target_type Core.Current_target in
  let right = build_expression state value in
  let bound = fresh_synthetic_local state in
  let bound_value =
    synthetic_expression state ~origin:value.id right.type_
      (Use (Local { local = bound; type_ = right.type_; origin = value.id }))
  in
  let make_built_in operation : Core.kind * Core.operand =
    (Operator { operation; arguments = [ current; bound_value ] }, Value right)
  in
  let kind, right_operand =
    match state.tables.calls.(written.id) with
    | Some ({ callee = Trait_method { trait; name; self_type; _ }; _ } as recorded) -> (
        match find_built_in_operation trait name self_type with
        | Some operation -> make_built_in operation
        | None ->
            let read_argument_mode index =
              match
                List.find_opt
                  (fun (argument : Tables.argument) -> argument.core_argument_index = index)
                  recorded.arguments
              with
              | Some argument -> argument.mode
              | None -> Types.Read
            in
            ( Call
                {
                  callee = convert_callee recorded.callee;
                  arguments =
                    [
                      Passed
                        { mode = read_argument_mode 0; value = Value current; mode_keyword = None };
                      Passed
                        {
                          mode = read_argument_mode 1;
                          value = build_operand (read_argument_mode 1) bound_value;
                          mode_keyword = None;
                        };
                    ];
                  lends = None;
                  uses = recorded.uses;
                },
              build_operand (read_argument_mode 1) right ))
    | Some _ -> bug "a compound assignment's call is not a trait method call"
    | None -> make_built_in (convert_to_operation operation)
  in
  Compound_assign
    {
      target = place;
      operand = right_operand;
      bound;
      value = synthetic_expression state ~origin:written.id target_type kind;
    }

let rec lend_statements state (mode : Types.mode) (value : Core.expression) : Core.statement list =
  let make_statement kind : Core.statement list =
    [ { id = fresh_node_id state; origin = value.origin; kind } ]
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
  | _ -> make_statement (Yield { mode; part = build_operand mode value })

and lend_block state mode (body : Core.block) : Core.block =
  match body.value with
  | None -> body
  | Some value -> { statements = body.statements @ lend_statements state mode value; value = None }

let rec is_fixed_place : Core.place -> bool = function
  | Local _ | Constant _ -> true
  | Field { base; _ } -> is_fixed_place base
  | Lent _ | Temporary _ -> false

let build_collection_place state (iterable : expression) (mode : Types.mode) :
    Core.place * (type_:Types.ty -> Core.block -> Core.kind) option =
  let collection = build_expression state iterable in
  match collection.kind with
  | Use place when is_fixed_place place -> (place, None)
  | _ ->
      let local = fresh_synthetic_local state and origin = iterable.id in
      let scrutinee = build_operand mode collection in
      let pattern : Core.pattern =
        {
          id = fresh_node_id state;
          origin;
          type_ = collection.type_;
          kind =
            Bind
              {
                local;
                name = "collection";
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
    ~(element : Tables.call) ~(lends : Types.mode) : Core.elements =
  let uint64 = Types.builtin UInt64 in
  let local = fresh_synthetic_local state in
  let make_receiver mode : Core.argument =
    Passed { mode; value = Place collection; mode_keyword = None }
  in
  let position =
    synthetic_expression state ~origin uint64 (Use (Local { local; type_ = uint64; origin }))
  in
  {
    count =
      synthetic_expression state ~origin uint64
        (Call
           {
             callee = convert_callee count.callee;
             arguments = [ make_receiver Read ];
             lends = None;
             uses = count.uses;
           });
    position =
      {
        id = fresh_node_id state;
        origin;
        type_ = uint64;
        kind = Bind { local; name = "position"; is_var = false; mode = Own };
      };
    element =
      Lent
        (synthetic_expression state ~origin element.callee_result
           (Call
              {
                callee = convert_callee element.callee;
                arguments =
                  [
                    make_receiver lends;
                    Passed { mode = Read; value = build_operand Read position; mode_keyword = None };
                  ];
                lends = Some lends;
                uses = element.uses;
              }));
  }

let quantify_over_elements state (collection : expression) ~count ~element ~lends ~origin quantified
    : Core.kind =
  let place, wrap = build_collection_place state collection lends in
  let kind = quantified (build_elements state ~origin:collection.id place ~count ~element ~lends) in
  match wrap with
  | None -> kind
  | Some wrap ->
      wrap ~type_:Types.bool
        { statements = []; value = Some (synthetic_expression state ~origin Types.bool kind) }

let build_cursor_next state (cursor : Types.ty) : Core.callee =
  let trait = trait_reference Impls.cursor_trait in
  match implements state cursor trait with
  | Some implementation ->
      Trait_method
        {
          trait;
          name = "next";
          receiver = Mut;
          self_type = cursor;
          type_arguments = [];
          evidence = convert_evidence (evidence_of implementation);
        }
  | None -> bug "a loop iterates over `%s`, which does not implement `Cursor`" (Types.show cursor)

let build_for_loop state (written : statement) (iterable : expression) ~pattern ~clauses ~body ~mode
    : Core.statement_kind =
  let make_loop iteration : Core.statement_kind = For { pattern; iteration; clauses; body; mode } in
  match (state.tables.loops.(written.id), iterable.kind) with
  | Some (Integer_range { inclusive; _ }), Range { start = Some start; stop = Some stop; _ } ->
      let start = build_expression state start in
      make_loop (Integer_range { start; stop = build_expression state stop; inclusive })
  | Some (Elements { count; element; lends }), _ -> (
      let place, wrap = build_collection_place state iterable lends in
      let elements_loop =
        make_loop (Elements (build_elements state ~origin:iterable.id place ~count ~element ~lends))
      in
      match wrap with
      | None -> elements_loop
      | Some wrap ->
          let statement : Core.statement =
            { id = fresh_node_id state; origin = written.id; kind = elements_loop }
          in
          Evaluate
            (synthetic_expression state ~origin:written.id Types.unit
               (wrap ~type_:Types.unit { statements = [ statement ]; value = None })))
  | Some (Pulled { cursor; cursor_call; remaining }), _ -> (
      let collection = build_expression state iterable in
      let pulled =
        match cursor_call with
        | None -> collection
        | Some cursor_call ->
            synthetic_expression state ~origin:iterable.id cursor
              (Call
                 {
                   callee = convert_callee cursor_call.callee;
                   arguments =
                     [
                       Passed
                         { mode = Own; value = build_operand Own collection; mode_keyword = None };
                     ];
                   lends = None;
                   uses = cursor_call.uses;
                 })
      in
      let next = build_cursor_next state cursor in
      let states_measure = List.exists (function Core.Decreases _ -> true | _ -> false) clauses in
      let make_cursor_loop ?remaining (place : Core.place) : Core.statement_kind =
        let measure =
          Option.map
            (fun (remaining : Tables.call) ->
              Core.Decreases
                [
                  synthetic_expression state ~origin:iterable.id (Types.builtin UInt64)
                    (Call
                       {
                         callee = convert_callee remaining.callee;
                         arguments =
                           [ Passed { mode = Read; value = Place place; mode_keyword = None } ];
                         lends = None;
                         uses = remaining.uses;
                       });
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
      match (pulled.kind, if states_measure then None else remaining) with
      | Use place, remaining when is_fixed_place place -> make_cursor_loop ?remaining place
      | _, None -> make_cursor_loop (place_of pulled)
      | _, Some remaining ->
          let local = fresh_synthetic_local state and origin = iterable.id in
          let binding : Core.pattern =
            {
              id = fresh_node_id state;
              origin;
              type_ = pulled.type_;
              kind = Bind { local; name = "cursor"; is_var = true; mode = Own };
            }
          in
          let statement : Core.statement =
            {
              id = fresh_node_id state;
              origin = written.id;
              kind = make_cursor_loop ~remaining (Local { local; type_ = pulled.type_; origin });
            }
          in
          Evaluate
            (synthetic_expression state ~origin:written.id Types.unit
               (Match
                  {
                    scrutinees = [ Value pulled ];
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
  | _ -> bug "the checker recorded no iteration for a `for` loop"

let convert_resource state (written : Syntax.resource) : Core.resource =
  let resolve_capability (path : path_type) =
    match State.target state path.path.last with
    | Some (Definition (Capability, capability)) -> capability
    | _ -> bug "`calls` names something that is not a capability"
  in
  match written with
  | Time -> Time
  | Allocations -> Allocations
  | Allocated_bytes -> Allocated_bytes
  | Calls (Call_parameter name) -> (
      match State.target state name with
      | Some (Local id) -> Calls (Function_parameter (Named id))
      | _ -> bug "`calls(%s)` names no parameter" name.text)
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
      | Finite -> Finite
      | Big_o value -> Order_of (build_expression state value)
      | At_most value -> At_most (build_expression state value)
      | Exactly value -> Exactly (build_expression state value));
  }

let build_loop_clause state (clause : loop_clause) : Core.loop_clause =
  match clause.kind with
  | Invariant value -> Invariant (build_expression state value)
  | Loop_decreases measures -> Decreases (List.map (build_expression state) measures)
  | Loop_cost written -> Cost (build_cost state ~origin:clause.id written)

let build_try state (value : expression) (inner : expression) ~(output : Types.ty) : Core.kind =
  let scrutinee = build_expression state inner in
  let read_variants (type_ : Types.ty) =
    match type_ with
    | Types.Named { path; arguments } -> (
        match Members.variants state.lookups path arguments with
        | Some [ success; failure ] -> (success, failure)
        | _ -> bug "`?` on `%s`" (Types.show type_))
    | _ -> bug "`?` on `%s`" (Types.show type_)
  in
  let success, failure = read_variants scrutinee.type_ in
  let _, returned_failure = read_variants output in
  let make = synthetic_expression state ~origin:value.id in
  let bind_fields (variant : Types.variant) : Core.pattern * (string * Core.expression) list =
    let fields =
      List.map
        (fun (field : Types.field) -> (field, fresh_synthetic_local state))
        (Option.value ~default:[] variant.fields)
    in
    ( {
        id = fresh_node_id state;
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
                        id = fresh_node_id state;
                        origin = value.id;
                        type_ = field.field_type;
                        kind = Bind { local; name = field.field_name; is_var = false; mode = Own };
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
      scrutinees = [ Value scrutinee ];
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
                                         (field.field_name, Some (Core.Value field_value)))
                                       (Option.value ~default:[] returned_failure.fields)
                                       failure_fields;
                                 })))));
            };
        ];
    }

let build_inserted_literal state ~origin (type_ : Types.ty) ~name ~insert
    (entries : Core.expression list list) : Core.kind =
  let path, type_arguments =
    match type_ with
    | Types.Named { path; arguments } -> (path, arguments)
    | _ -> bug "a set or map literal of type `%s`" (Types.show type_)
  in
  let make = synthetic_expression state ~origin in
  let make_statement kind : Core.statement = { id = fresh_node_id state; origin; kind } in
  let make_call name receiver arguments result =
    make result
      (Call
         {
           callee = Function { path = Method { owner = path; name; receiver }; type_arguments };
           arguments;
           lends = None;
           uses = Types.no_capabilities;
         })
  in
  let capacity = make (Types.builtin UInt64) (Integer (Z.of_int (List.length entries))) in
  let created =
    make_call "with_capacity" Static
      [ Passed { mode = Read; value = Value capacity; mode_keyword = None } ]
      type_
  in
  match entries with
  | [] -> created.kind
  | _ ->
      let local = fresh_synthetic_local state in
      let collection : Core.place = Local { local; type_; origin } in
      let bind =
        make_statement
          (Let
             {
               pattern =
                 {
                   id = fresh_node_id state;
                   origin;
                   type_;
                   kind = Bind { local; name; is_var = true; mode = Own };
                 };
               value = Value created;
               else_ = None;
             })
      in
      let inserts =
        List.map
          (fun entry ->
            make_statement
              (Evaluate
                 (make_call insert Mut
                    (Passed { mode = Mut; value = Place collection; mode_keyword = None }
                    :: List.map
                         (fun argument : Core.argument ->
                           Passed { mode = Own; value = Value argument; mode_keyword = None })
                         entry)
                    Types.unit)))
          entries
      in
      Block { statements = bind :: inserts; value = Some (make type_ (Use collection)) }

let build_collection_literal state (value : expression) (elements : Core.expression list) :
    Core.kind =
  match read_type state value with
  | Types.Named { path; arguments = [ Types.Type element ] } when Well_known.is List path ->
      build_list_literal state ~origin:value.id element elements
  | Types.Named { path; _ } as type_ when Well_known.is Set path ->
      build_inserted_literal state ~origin:value.id type_ ~name:"set" ~insert:"insert"
        (List.map (fun element -> [ element ]) elements)
  | Types.Named { path; _ } when Intrinsic.builtin_of_path path = Some Array ->
      Collection_literal { elements; construction = Array }
  | Types.Named { path; _ } when Well_known.is Sequence path || Well_known.is Finite_set path ->
      Collection_literal { elements; construction = Specification_only }
  | type_ -> bug "a collection literal of type `%s`" (Types.show type_)

let build_map_literal state (value : expression)
    (entries : (Core.expression * Core.expression) list) : Core.kind =
  match read_type state value with
  | Types.Named { path; _ } as type_ when Well_known.is Map path ->
      build_inserted_literal state ~origin:value.id type_ ~name:"map" ~insert:"insert_absent"
        (List.map (fun (key, entry) -> [ key; entry ]) entries)
  | Types.Named { path; _ } when Well_known.is Finite_map path -> Map_literal { entries }
  | type_ -> bug "a map literal of type `%s`" (Types.show type_)

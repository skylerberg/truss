let raise_bug format = Compiler_bug.raise_bug ~stage:"MIR" format

let rec holds_break (block : Tree.block) =
  List.exists
    (fun (statement : Tree.statement) ->
      match statement.kind with
      | Jump Break -> true
      | While _ | For _ -> false
      | Basic _ | Choose _ | Assert_by_bit_vector _ | Fork _ | Resume _ | Yield _
      | Jump (Return _ | Continue | Cancel _ | Unreachable | Written_unreachable | Todo) ->
          List.exists holds_break (Walk.list_nested_blocks statement))
    block.statements

let project (place : Tree.place) projection =
  { place with projections = place.projections @ [ projection ] }

let ( let* ) = Option.bind

let compute_core_operand_type : Core.operand -> Types.ty = function
  | Place place -> Core_walk.compute_place_type place
  | Value value -> value.type_

let compute_operand_origin : Core.operand -> Core.origin = function
  | Place place -> Core_walk.compute_place_origin place
  | Value value -> value.origin

module In_order = struct
  type 'value t = {
    slots : int;
    origin : Core.origin option;
    evaluate : count:int -> index:int -> loans:int list ref -> 'value option;
  }

  let pure value =
    { slots = 0; origin = None; evaluate = (fun ~count:_ ~index:_ ~loans:_ -> Some value) }

  let evaluate_operand_with builder evaluate type_ origin =
    {
      slots = 1;
      origin = Some origin;
      evaluate =
        (fun ~count ~index ~loans ->
          let* value, extra = evaluate () in
          if count > 1 then begin
            let value = Emitter.hold_operand builder value type_ origin in
            (match value with
            | Constant _ | Take _ -> ()
            | _ ->
                if index < count - 1 then
                  loans := Emitter.start_loan builder value Read Operand_evaluation origin :: !loans);
            Some (value, extra)
          end
          else Some (value, extra));
    }

  let map transform evaluation =
    {
      evaluation with
      evaluate =
        (fun ~count ~index ~loans ->
          Option.map transform (evaluation.evaluate ~count ~index ~loans));
    }

  let map2 combine first second =
    {
      slots = first.slots + second.slots;
      origin = (match first.origin with None -> second.origin | origin -> origin);
      evaluate =
        (fun ~count ~index ~loans ->
          let* first_value = first.evaluate ~count ~index ~loans in
          let* second_value = second.evaluate ~count ~index:(index + first.slots) ~loans in
          Some (combine first_value second_value));
    }

  let evaluate_operand builder evaluate type_ origin =
    map fst
      (evaluate_operand_with builder
         (fun () -> Option.map (fun value -> (value, ())) (evaluate ()))
         type_ origin)

  let all evaluations = List.fold_right (map2 List.cons) evaluations (pure [])

  let run builder evaluation =
    let loans = ref [] in
    let value = evaluation.evaluate ~count:evaluation.slots ~index:0 ~loans in
    Option.iter (Emitter.end_loans builder (List.rev !loans)) evaluation.origin;
    value
end

let rec runs_code (place : Core.place) =
  match place with
  | Local _ | Constant _ -> false
  | Field { base; _ } -> runs_code base
  | Lent _ | Temporary _ -> true

let rec is_function_expression (written : Core.expression) =
  match written.kind with
  | Function_value _ | Lambda _ -> true
  | Convert { conversion = Widen; value } -> is_function_expression value
  | _ -> false

let is_unit (type_ : Types.ty) = Types.equal type_ Types.unit
let diverges (type_ : Types.ty) = type_ = Types.Never

let rec make_field_path (place : Tree.place) = function
  | [] -> place
  | field :: rest -> make_field_path (project place (Field field)) rest

let rec list_extended_temporaries (value : Core.operand) =
  match value with
  | Place base -> list_extended_by_base base
  | Value value -> list_extended_by value

and list_extended_by (value : Core.expression) =
  match value.kind with
  | Slice { base; _ } -> list_extended_by_base base
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:list_extended_temporaries field)
        fields
  | Record_update { updates; _ } ->
      List.concat_map (fun (_, update) -> list_extended_by update) updates
  | Collection_literal { elements; construction = Array } ->
      List.concat_map list_extended_by elements
  | _ -> []

and list_extended_by_base (base : Core.place) =
  match base with
  | Temporary written -> written.id :: list_extended_by written
  | Field { base; _ } -> list_extended_by_base base
  | Local _ | Constant _ | Lent _ -> []

let list_names (written : Core.expression) =
  let names = ref [] in
  Core_walk.walk_expression
    {
      Core_walk.ignore_all with
      place =
        (function Local { local; origin; _ } -> names := (local, origin) :: !names | _ -> ());
    }
    written;
  List.rev !names

let make_literal_place text type_ = { Tree.root = Literal { text; type_ }; projections = [] }

let read_literal text type_ origin =
  Tree.Borrow { place = make_literal_place text type_; type_; mode = Read; origin }

let lower_pattern_constant (pattern : Core.pattern) (value : Core.pattern_constant) : Tree.operand =
  let type_ = pattern.type_ in
  match value with
  | Boolean_constant value -> Constant { value = Boolean value; type_ }
  | Integer_constant value -> Constant { value = Integer value; type_ }
  | String_constant text -> read_literal text type_ pattern.origin
  | Named_constant path ->
      Use { place = { root = Constant path; projections = [] }; type_; origin = pattern.origin }

let lower_range_bound (pattern : Core.pattern) (bound : Core.range_bound) : Tree.operand =
  lower_pattern_constant pattern
    (match bound with
    | Integer_bound value -> Integer_constant value
    | Constant_bound path -> Named_constant path)

let rec lower_expression builder (node : Core.expression) : Tree.operand option =
  let origin = node.origin in
  let hold value = Emitter.hold builder node.type_ origin value in
  if not (Emitter.reaches builder) then None
  else
    match node.kind with
    | Integer value -> Some (Constant { value = Integer value; type_ = node.type_ })
    | Float value -> Some (Constant { value = Float value; type_ = node.type_ })
    | Boolean value -> Some (Constant { value = Boolean value; type_ = node.type_ })
    | String text -> hold (Copy (read_literal text node.type_ origin))
    | Template { literals; call = { kind = Call called; _ } } ->
        let* call = lower_call builder called ~node:node.id ~origin:node.origin in
        let local = Emitter.allocate_temporary builder node.type_ origin in
        Emitter.emit builder
          (Basic (Template { destination = Emitter.make_local_place local; literals; call }))
          origin;
        Some
          (Tree.Use
             { place = Emitter.make_local_place local; type_ = node.type_; origin = node.origin })
    | Template _ -> raise_bug "a tagged template whose value is not a call"
    | Use place_ ->
        let* place_ = lower_place builder place_ in
        Some (Tree.Use { place = place_; type_ = node.type_; origin = node.origin })
    | Copy copied ->
        let* copied = lower_operand builder Read copied in
        hold (Copy copied)
    | Function_value _ | Lambda _ ->
        Option.map fst (lower_function_expression builder node ~is_argument:false)
    | Value_parameter parameter -> hold (Value_parameter parameter)
    | Construct { variant; fields } ->
        let* fields = construct_fields builder fields in
        hold (Construct { variant; fields; type_ = node.type_ })
    | Collection_literal { elements; construction = Array } ->
        let* elements = lower_operands builder elements in
        hold (Array elements)
    | Record_update { base; updates } ->
        let* base_value, update_values =
          In_order.run builder
            (In_order.map2
               (fun base_value update_values -> (base_value, update_values))
               (plan_expression builder base)
               (In_order.all
                  (List.map
                     (fun (fields, (written : Core.expression)) ->
                       In_order.map
                         (fun value -> (fields, written, value))
                         (plan_expression builder written))
                     updates)))
        in
        let local = Emitter.allocate_temporary builder node.type_ origin in
        Emitter.assign builder (Emitter.make_local_place local) (Operand base_value) origin;
        List.iter
          (fun (fields, (written : Core.expression), value) ->
            Emitter.assign builder
              (make_field_path (Emitter.make_local_place local) fields)
              (Operand value) written.origin)
          update_values;
        Some
          (Tree.Use
             { place = Emitter.make_local_place local; type_ = node.type_; origin = node.origin })
    | Slice { base; callee; bounds } ->
        let* callee = lower_callee builder callee in
        let* (receiver, base_place), bounds =
          In_order.run builder
            (In_order.map2
               (fun receiver bounds -> (receiver, bounds))
               (plan_borrow builder base)
               (In_order.all (List.map (plan_argument builder) bounds)))
        in
        let call =
          {
            Tree.callee;
            arguments = Passed { mode = Read; value = receiver; function_ = None } :: bounds;
            uses = Types.no_capabilities;
            node = node.id;
            origin = node.origin;
          }
        in
        let local = Emitter.allocate_temporary builder node.type_ origin in
        Emitter.emit builder
          (Basic
             (Slice
                {
                  destination = Emitter.make_local_place local;
                  base = Emitter.borrow_place builder base_place;
                  base_type = Core_walk.compute_place_type base;
                  call;
                }))
          origin;
        Some
          (Tree.Use
             { place = Emitter.make_local_place local; type_ = node.type_; origin = node.origin })
    | Call called -> lower_call_value builder node called
    | Operator { operation; arguments } ->
        let* operands = lower_operands builder arguments in
        let type_arguments =
          List.map (fun (argument : Core.expression) -> Types.Type argument.type_) arguments
        in
        hold (Operation { operation; type_arguments; operands })
    | Compare { comparison; left; right } ->
        let* left, right = evaluate_pair builder left right in
        hold (Compare { comparison; left; right })
    | Not inner ->
        let* inner = lower_expression builder inner in
        hold (Not inner)
    | And _ | Or _ | Implies _ | Matches _ -> lower_truth builder node
    | Convert { conversion = Widen; value = converted } when is_function_expression converted ->
        Option.map fst (lower_function_expression builder node ~is_argument:false)
    | Convert { conversion; value = converted } ->
        let* value = lower_expression builder converted in
        hold (Convert { conversion; value; converts_function_expression = false })
    | To_any { value; trait; evidence } ->
        let* value = lower_expression builder value in
        hold (To_any { value; trait; evidence })
    | If { condition = tested; then_; else_; binds_lent_part } ->
        let lowered =
          Emitter.run_in_condition_scope builder ~binds_lent_part (fun () ->
              lower_expression builder tested)
        in
        let* condition = lowered.value in
        let result = allocate_value_local builder node in
        let lower_arm ?held ended (body : Core.block option) =
          Emitter.build_block builder (fun () ->
              Emitter.end_scope builder ended tested.origin;
              Emitter.run_in_scope ?held builder origin (fun () ->
                  match (Option.map (lower_block builder) body, result) with
                  | Some (Some value), Some local ->
                      Emitter.assign builder (Emitter.make_local_place local) (Operand value) origin;
                      Some
                        (Tree.Use
                           { place = Emitter.make_local_place local; type_ = node.type_; origin })
                  | Some None, _ -> None
                  | (Some (Some _) | None), _ -> Some Emitter.unit_value))
        in
        let then_ = lower_arm ~held:lowered.held_if_true lowered.ended_if_true (Some then_) in
        let else_ = lower_arm lowered.ended_if_false else_ in
        lower_choice builder node [ then_; else_ ]
          (Tree.Conditional { condition; then_; else_; if_condition = Some tested.origin })
    | Match { scrutinees; arms } -> match_ builder node scrutinees arms
    | Block inner -> Emitter.run_in_value_scope builder origin (fun () -> lower_block builder inner)
    | Provide { implementations; body } ->
        let* provided =
          In_order.run builder
            (In_order.all
               (List.map
                  (fun (implementation : Core.implementation) ->
                    In_order.map
                      (fun value ->
                        {
                          Tree.mode = implementation.mode;
                          value;
                          type_ = implementation.type_;
                          provides = implementation.provides;
                          origin = implementation.origin;
                        })
                      (In_order.evaluate_operand builder
                         (fun () -> lower_operand builder implementation.mode implementation.value)
                         implementation.type_ implementation.origin))
                  implementations))
        in
        Emitter.emit builder
          (Basic (Provide { provided; can_use_tasks = Core_walk.can_use_tasks body }))
          origin;
        Emitter.run_in_value_scope ~provides:true builder origin (fun () ->
            List.iter
              (fun (provided : Tree.provided) ->
                match provided.value with
                | Borrow _ ->
                    ignore
                      (Emitter.start_loan builder provided.value
                         (if provided.mode = Mut then Mut else Read)
                         Provide_body provided.origin)
                | _ -> ())
              provided;
            lower_block builder body)
    | Return returned ->
        (match returned with
        | None -> Emitter.return_ builder None origin
        | Some returned ->
            Option.iter
              (fun value -> Emitter.return_ builder (Some value) origin)
              (lower_expression builder returned));
        None
    | Break ->
        Emitter.break_ builder origin;
        None
    | Continue ->
        Emitter.continue_ builder origin;
        None
    | Todo ->
        Emitter.jump builder Todo origin;
        None
    | Unreachable ->
        Emitter.jump builder Written_unreachable origin;
        None
    | Echo inner ->
        let* value = lower_expression builder inner in
        let local = Emitter.allocate_temporary builder inner.type_ origin in
        Emitter.assign builder (Emitter.make_local_place local) (Operand value) origin;
        Emitter.emit builder
          (Basic
             (Echo
                (Borrow
                   {
                     place = Emitter.make_local_place local;
                     type_ = inner.type_;
                     mode = Read;
                     origin;
                   })))
          origin;
        Some
          (Tree.Use
             { place = Emitter.make_local_place local; type_ = node.type_; origin = node.origin })
    | Current_target -> (
        match Emitter.compound_target builder with
        | Some target -> Some (Take { place = target; type_ = node.type_; origin = node.origin })
        | None -> raise_bug "the old value of a target outside a compound assignment")
    | Quantified { quantifier; binder; body } when Emitter.is_specification builder ->
        lower_quantified builder node quantifier binder body
    | Quantified { quantifier; binder = Over_range { pattern; start; stop; inclusive }; body } ->
        lower_quantifier_loop builder node quantifier body (fun ~loop ~each ->
            lower_range_loop builder ~origin ~pattern ~start ~stop ~inclusive ~loop ~each)
    | Quantified { quantifier; binder = Over_elements { pattern; elements }; body } ->
        lower_quantifier_loop builder node quantifier body (fun ~loop ~each ->
            lower_elements_loop builder ~origin ~pattern ~elements ~loop ~each)
    | Collection_literal { elements; construction = Specification_only } ->
        let* elements = lower_operands builder elements in
        hold (Array elements)
    | Map_literal { entries } ->
        let* entries =
          In_order.run builder
            (In_order.all
               (List.map
                  (fun (key, value) ->
                    In_order.map2
                      (fun key value -> (key, value))
                      (plan_expression builder key) (plan_expression builder value))
                  entries))
        in
        hold (Specification (Map entries))
    | Result -> hold (Specification Result)
    | Yielded -> hold (Specification Yielded)
    | Old inner -> Emitter.run_in_old builder (fun () -> lower_expression builder inner)
    | Identical (first, second) ->
        let* first, second = evaluate_pair builder first second in
        hold (Specification (Identical (first, second)))
    | Specification_function { function_; arguments } ->
        let rec compute_unconverted_type (argument : Core.expression) =
          match argument.kind with
          | Convert { conversion = To_integer; value } -> compute_unconverted_type value
          | _ -> argument.type_
        in
        let unconverted = List.map compute_unconverted_type arguments in
        let* arguments = lower_operands builder arguments in
        hold (Specification (Applied { function_; arguments; unconverted }))
    | Method_cost { metric; method_ } ->
        let* method_ = lower_callee builder method_ in
        hold (Specification (Method_cost { metric; method_ }))
    | Quantified _ -> raise_bug "a quantifier over a type or a collection in code that runs"

and plan_expression builder (node : Core.expression) =
  In_order.evaluate_operand builder (fun () -> lower_expression builder node) node.type_ node.origin

and plan_operand builder mode (passed : Core.operand) =
  In_order.evaluate_operand builder
    (fun () -> lower_operand builder mode passed)
    (compute_core_operand_type passed)
    (compute_operand_origin passed)

and lower_operands builder nodes =
  In_order.run builder (In_order.all (List.map (plan_expression builder) nodes))

and evaluate_pair builder (first : Core.expression) (second : Core.expression) =
  In_order.run builder
    (In_order.map2
       (fun first second -> (first, second))
       (plan_expression builder first) (plan_expression builder second))

and construct_fields builder fields =
  In_order.run builder
    (In_order.all
       (List.map
          (fun (name, field) ->
            match field with
            | None -> In_order.pure (name, None)
            | Some (field : Core.operand) ->
                In_order.map
                  (fun value -> (name, Some value))
                  (In_order.evaluate_operand builder
                     (fun () ->
                       match field with
                       | Place _ ->
                           raise_bug
                             "a constructor field that is a place, in a construct that no lending \
                              method lends"
                       | Value value -> lower_expression builder value)
                     (compute_core_operand_type field) (compute_operand_origin field)))
          fields))

and lower_yielded builder (mode : Types.mode) (part : Core.operand) : Tree.yielded option =
  let rec lends : Core.operand -> bool = function
    | Place _ -> true
    | Value { kind = Construct { fields; _ }; _ } ->
        List.exists (fun (_, field) -> Option.fold ~none:false ~some:lends field) fields
    | Value _ -> false
  in
  match part with
  | Value { kind = Construct _; _ } when lends part ->
      let rec plan_part (field : Core.operand) : Tree.yielded In_order.t =
        match field with
        | Value ({ kind = Construct { variant; fields }; _ } as node) when lends field ->
            In_order.map
              (fun fields -> Tree.Built { variant; fields; type_ = node.type_ })
              (In_order.all
                 (List.map
                    (fun (name, field) ->
                      match field with
                      | None -> In_order.pure (name, None)
                      | Some field ->
                          In_order.map (fun built -> (name, Some built)) (plan_part field))
                    fields))
        | _ -> In_order.map (fun value -> Tree.Part value) (plan_operand builder mode field)
      in
      In_order.run builder (plan_part part)
  | _ -> Option.map (fun value -> Tree.Part value) (lower_operand builder mode part)

and lower_operand builder (mode : Types.mode) (passed : Core.operand) =
  match passed with
  | Place written ->
      let* passed = lower_place builder written in
      Some (make_borrow written passed mode)
  | Value value -> lower_expression builder value

and make_borrow (written : Core.place) (place : Tree.place) mode =
  Borrow
    {
      place;
      type_ = Core_walk.compute_place_type written;
      mode;
      origin = Core_walk.compute_place_origin written;
    }

and plan_borrow builder (written : Core.place) =
  In_order.evaluate_operand_with builder
    (fun () ->
      let* place = lower_place builder written in
      Some (make_borrow written place Read, place))
    (Core_walk.compute_place_type written)
    (Core_walk.compute_place_origin written)

and lower_place builder (written : Core.place) : Tree.place option =
  if not (Emitter.reaches builder) then None
  else
    match written with
    | Local { local; type_; origin } when Emitter.reads_entry builder local ->
        let entry = Emitter.allocate_temporary builder type_ origin in
        Emitter.assign builder (Emitter.make_local_place entry)
          (Specification (Entry (Emitter.obtain_free_source builder local ~type_ ~origin)))
          origin;
        Some (Emitter.make_local_place entry)
    | Local { local; type_; origin } ->
        Some (Emitter.make_local_place (Emitter.obtain_free_source builder local ~type_ ~origin))
    | Constant { path; _ } -> Some { root = Constant path; projections = [] }
    | Field { base; field; _ } ->
        let* base = lower_place builder base in
        Some (project base (Field field))
    | Lent lending -> lower_lent builder lending ~duration:Tree.Rest_of_statement
    | Temporary { kind = String text; type_; _ } -> Some (make_literal_place text type_)
    | Temporary written ->
        let* value = lower_expression builder written in
        let local =
          Emitter.allocate_place_temporary builder ~node:written.id written.type_ written.origin
        in
        Emitter.assign builder (Emitter.make_local_place local) (Operand value) written.origin;
        Some (Emitter.make_local_place local)

and lower_lent builder (lending : Core.expression) ~duration : Tree.place option =
  match lending.kind with
  | Call ({ lends = Some mode; _ } as called) ->
      let* call = lower_call builder called ~node:lending.id ~origin:lending.origin in
      let part = Emitter.allocate_local builder (Lent mode) lending.type_ lending.origin in
      Emitter.add_temporary builder part;
      Emitter.emit builder (Basic (Lend { part; call })) lending.origin;
      (match call.arguments with
      | Passed { mode; value = (Borrow _ | Use _) as receiver; _ } :: _ ->
          ignore
            (Emitter.start_loan builder receiver
               (if mode = Mut then Mut else Read)
               duration lending.origin)
      | _ -> ());
      Some (Emitter.make_local_place part)
  | Call _ -> raise_bug "a lent place whose call does not lend"
  | _ -> raise_bug "a lent place that is not a call"

and lower_function_expression builder (node : Core.expression) ~is_argument :
    (Tree.operand * Tree.function_argument) option =
  let origin = node.origin in
  let hold value = Emitter.hold builder node.type_ origin value in
  match node.kind with
  | Function_value { path; instantiation } ->
      let* value = hold (Function_value { path; instantiation; is_argument }) in
      Some (value, Tree.Function_reference { path; origin })
  | Lambda { parameters; captures; body; _ } ->
      let index = lower_lambda builder parameters captures body in
      let* value =
        hold
          (Lambda
             {
               is_argument;
               body = index;
               captures =
                 List.map
                   (fun (capture : Core.capture) ->
                     {
                       Tree.local = capture.local;
                       type_ = capture.type_;
                       place =
                         Emitter.make_local_place
                           (Emitter.obtain_free_source builder capture.local ~type_:capture.type_
                              ~origin);
                     })
                   captures;
             })
      in
      Some (value, Tree.Lambda_expression { body = index; origin; type_ = node.type_ })
  | Convert { conversion = Widen as conversion; value = converted } ->
      let* value, function_ = lower_function_expression builder converted ~is_argument in
      let* value =
        hold
          (Convert
             {
               conversion;
               value;
               converts_function_expression =
                 (match converted.kind with Function_value _ | Lambda _ -> true | _ -> false);
             })
      in
      Some (value, function_)
  | _ -> raise_bug "a function expression that is no function and no lambda"

and lower_callee builder (callee : Core.callee) : Tree.callee option =
  Core_walk.traverse_indirect (lower_operand builder Read) callee

and lower_call builder (called : Core.call) ~node ~origin : Tree.call option =
  let* callee = lower_callee builder called.callee in
  let* arguments =
    In_order.run builder (In_order.all (List.map (plan_argument builder) called.arguments))
  in
  Some { Tree.callee; arguments; uses = called.uses; node; origin }

and plan_argument builder (argument : Core.argument) =
  match argument with
  | Default -> In_order.pure Tree.Default
  | Passed { mode; value } ->
      In_order.map
        (fun (value, function_) -> Tree.Passed { mode; value; function_ })
        (In_order.evaluate_operand_with builder
           (fun () ->
             match value with
             | Value written when is_function_expression written ->
                 Option.map
                   (fun (passed, function_) -> (passed, Some function_))
                   (lower_function_expression builder written ~is_argument:true)
             | Place _ | Value _ ->
                 Option.map (fun passed -> (passed, None)) (lower_operand builder mode value))
           (compute_core_operand_type value) (compute_operand_origin value))

and lower_call_value builder (node : Core.expression) (called : Core.call) =
  let origin = node.origin in
  match called.callee with
  | Intrinsic { operation = Scalar operation; type_arguments } ->
      let* operands =
        In_order.run builder
          (In_order.all
             (List.map
                (function
                  | Core.Passed { value; mode; _ } -> plan_operand builder mode value
                  | Default -> raise_bug "a primitive operation with a default argument")
                called.arguments))
      in
      Emitter.hold builder node.type_ origin (Operation { operation; type_arguments; operands })
  | _ ->
      let* call = lower_call builder called ~node:node.id ~origin:node.origin in
      if diverges node.type_ then begin
        Emitter.emit builder (Basic (Call { destination = None; call })) origin;
        Emitter.jump builder Unreachable origin;
        None
      end
      else if is_unit node.type_ then begin
        Emitter.emit builder (Basic (Call { destination = None; call })) origin;
        Some (Tree.Constant { value = Unit; type_ = Types.unit })
      end
      else
        let local = Emitter.allocate_temporary builder node.type_ origin in
        Emitter.emit builder
          (Basic (Call { destination = Some (Emitter.make_local_place local); call }))
          origin;
        Some
          (Use { place = Emitter.make_local_place local; type_ = node.type_; origin = node.origin })

and lower_choice builder (node : Core.expression) (blocks : Tree.block list) choice =
  let type_ = if diverges node.type_ then Types.unit else node.type_ in
  let held = Emitter.hold_choice builder type_ node.origin choice in
  if List.exists (fun (block : Tree.block) -> block.value <> None) blocks then held
  else begin
    Emitter.mark_unreachable builder;
    None
  end

and lower_truth builder (node : Core.expression) : Tree.operand option =
  let lower_connective connective (left : Core.expression) (right : Core.expression) =
    let* left = lower_expression builder left in
    let right = Emitter.build_block builder (fun () -> lower_expression builder right) in
    Emitter.hold_choice builder node.type_ node.origin (Connective { connective; left; right })
  in
  match node.kind with
  | And (left, right) -> lower_connective And left right
  | Or (left, right) -> lower_connective Or left right
  | Implies (left, right) -> lower_connective Implies left right
  | Matches { value; pattern } ->
      let* scrutinee = lower_scrutinee builder value in
      Emitter.run_binding_to_statement builder (fun () ->
          match_patterns builder [ pattern ]
            [ (scrutinee, compute_operand_origin value) ]
            node.origin)
  | _ -> raise_bug "a condition that is no short-circuit operator and no `is`"

and lower_pattern_tests ~bind_matched builder (patterns : Core.pattern list) places :
    Tree.operand option =
  let tested = ref [] in
  let branch_on value origin =
    match value with
    | Some left when Emitter.reaches builder ->
        tested := (left, Emitter.suspend_block builder, origin) :: !tested
    | _ -> ()
  in
  List.iter2 (fun pattern place -> test builder pattern place ~branch_on) patterns places;
  bind_matched ();
  List.fold_left
    (fun holds (left, enclosing, origin) ->
      let statements = Emitter.resume_block builder enclosing in
      match (holds, statements) with
      | None, _ -> None
      | Some (Tree.Constant { value = Boolean true; _ }), [] -> Some left
      | Some _, _ ->
          Emitter.hold_choice builder Types.bool origin
            (Connective { connective = And; left; right = { statements; value = holds } }))
    (Some (Constant { value = Boolean true; type_ = Types.bool }))
    !tested

and match_patterns ?(covers = false) builder (patterns : Core.pattern list) scrutinees origin :
    Tree.operand option =
  let places = List.map fst scrutinees in
  let bind_matched patterns () =
    List.iter2
      (fun pattern (place, scrutinee_origin) -> bind builder pattern place ~scrutinee_origin)
      patterns scrutinees
  in
  let rec lower_alternatives = function
    | [] -> raise_bug "a pattern with no alternative"
    | [ patterns ] when covers ->
        bind_matched patterns ();
        Some (Tree.Constant { value = Boolean true; type_ = Types.bool })
    | [ patterns ] ->
        lower_pattern_tests builder patterns places ~bind_matched:(bind_matched patterns)
    | patterns :: later ->
        let* left =
          lower_pattern_tests builder patterns places ~bind_matched:(bind_matched patterns)
        in
        let right = Emitter.build_block builder (fun () -> lower_alternatives later) in
        Emitter.hold_choice builder Types.bool origin (Connective { connective = Or; left; right })
  in
  lower_alternatives (expand_patterns patterns)

and match_ builder (node : Core.expression) scrutinees (arms : Core.arm list) : Tree.operand option
    =
  let origin = node.origin in
  let* scrutinee_values =
    In_order.run builder
      (In_order.all
         (List.map
            (fun (scrutinee : Core.operand) ->
              In_order.map (fun value -> (scrutinee, value)) (plan_operand builder Read scrutinee))
            scrutinees))
  in
  let evaluated = List.map snd scrutinee_values in
  let scrutinee_places =
    List.map
      (fun ((scrutinee : Core.operand), value) ->
        let origin = compute_operand_origin scrutinee in
        (lower_scrutinee_place builder value (compute_core_operand_type scrutinee) origin, origin))
      scrutinee_values
  in
  let result = allocate_value_local builder node in
  let left_by_arm_before = ref [] in
  let lower_case (arm : Core.arm) : Tree.case =
    Emitter.run_in_arm_scope builder @@ fun scope ->
    let tests =
      Emitter.build_block builder (fun () ->
          List.iter
            (fun (ended : Tree.statement) -> Emitter.emit builder ended.kind ended.origin)
            !left_by_arm_before;
          match_patterns builder arm.patterns scrutinee_places arm.origin)
    in
    let guard =
      Option.map
        (fun (guard : Core.expression) ->
          Emitter.build_block builder (fun () ->
              let loans =
                List.filter_map
                  (fun value ->
                    match value with
                    | Tree.Constant _ -> None
                    | _ ->
                        Some (Emitter.start_loan builder value Read Operand_evaluation arm.origin))
                  evaluated
              in
              let holds =
                Emitter.run_in_guard_scope builder guard.origin (fun () ->
                    lower_expression builder guard)
              in
              Emitter.end_loans builder loans arm.origin;
              holds))
        arm.guard
    in
    let value =
      Emitter.build_block builder (fun () ->
          if arm.patterns <> [] then
            Emitter.emit builder
              (Basic
                 (Matched
                    {
                      patterns =
                        List.map (fun (pattern : Core.pattern) -> pattern.origin) arm.patterns;
                    }))
              arm.origin;
          let value =
            match (lower_block builder arm.body, result) with
            | Some value, Some local ->
                Emitter.assign builder (Emitter.make_local_place local) (Operand value) arm.origin;
                Some
                  (Tree.Use { place = Emitter.make_local_place local; type_ = node.type_; origin })
            | Some _, None -> Some Emitter.unit_value
            | None, _ -> None
          in
          Emitter.end_scope builder scope arm.origin;
          value)
    in
    left_by_arm_before := Emitter.make_dead_statements scope arm.origin;
    { Tree.tests; guard; value }
  in
  let cases = List.map lower_case arms in
  lower_choice builder node (List.map (fun (case : Tree.case) -> case.value) cases) (Cases cases)

and allocate_value_local builder (node : Core.expression) =
  if is_unit node.type_ || diverges node.type_ then None
  else Some (Emitter.allocate_temporary builder node.type_ node.origin)

and lower_block builder (body : Core.block) : Tree.operand option =
  List.iter (lower_statement builder) body.statements;
  match body.value with
  | Some value -> lower_expression builder value
  | None -> if Emitter.reaches builder then Some Emitter.unit_value else None

and lower_body builder (body : Core.block) ~returns =
  let return_ value = Emitter.return_ builder (if returns then Some value else None) 0 in
  List.iter (lower_statement builder) body.statements;
  match body.value with
  | Some value ->
      Emitter.run_in_statement builder value.origin (fun () ->
          Option.iter return_ (lower_expression builder value))
  | None -> if Emitter.reaches builder then return_ Emitter.unit_value

and lower_scrutinee builder (matched : Core.operand) : Tree.place option =
  match matched with
  | Place written -> lower_place builder written
  | Value value ->
      let* value = lower_expression builder value in
      let local =
        Emitter.allocate_temporary builder
          (compute_core_operand_type matched)
          (compute_operand_origin matched)
      in
      Emitter.assign builder (Emitter.make_local_place local) (Operand value)
        (compute_operand_origin matched);
      Some (Emitter.make_local_place local)

and lower_scrutinee_place builder (value : Tree.operand) type_ origin : Tree.place =
  match value with
  | Borrow { place; _ } -> place
  | Use { place = { root = Local local; projections = [] } as place; _ }
    when (Emitter.lookup_local_info builder local).kind = Temporary ->
      place
  | Use _ | Take _ | Constant _ ->
      let local = Emitter.allocate_temporary builder type_ origin in
      Emitter.assign builder (Emitter.make_local_place local) (Operand value) origin;
      Emitter.make_local_place local

and test builder (pattern : Core.pattern) (scrutinee : Tree.place) ~branch_on =
  let origin = pattern.origin in
  let branch value = branch_on value origin in
  let read = Tree.Use { place = scrutinee; type_ = pattern.type_; origin = pattern.origin } in
  match pattern.kind with
  | Wildcard | Bind _ -> ()
  | Variant { variant; fields } ->
      branch (Emitter.hold builder Types.bool origin (Is_variant { place = scrutinee; variant }));
      List.iter
        (fun (field, inner) ->
          test builder inner (project scrutinee (Variant_field { variant; field })) ~branch_on)
        fields
  | Record fields ->
      List.iter
        (fun (field, inner) -> test builder inner (project scrutinee (Field field)) ~branch_on)
        fields
  | Literal value ->
      branch
        (Emitter.hold builder Types.bool origin
           (Compare
              { comparison = Equal; left = read; right = lower_pattern_constant pattern value }))
  | Range { start; stop; inclusive } ->
      branch
        (Emitter.hold builder Types.bool origin
           (Compare
              { comparison = Greater_equal; left = read; right = lower_range_bound pattern start }));
      branch
        (Emitter.hold builder Types.bool origin
           (Compare
              {
                comparison = (if inclusive then Less_equal else Less);
                left = read;
                right = lower_range_bound pattern stop;
              }))
  | Equal_to { value; equal } -> (
      match lower_callee builder equal with
      | Some callee when Emitter.reaches builder ->
          let local = Emitter.allocate_temporary builder Types.bool origin in
          Emitter.emit builder
            (Basic
               (Call
                  {
                    destination = Some (Emitter.make_local_place local);
                    call =
                      {
                        callee;
                        arguments =
                          [
                            Passed
                              {
                                mode = Read;
                                value =
                                  Borrow
                                    {
                                      place = scrutinee;
                                      type_ = pattern.type_;
                                      mode = Read;
                                      origin = pattern.origin;
                                    };
                                function_ = None;
                              };
                            Passed
                              {
                                mode = Read;
                                value = lower_pattern_constant pattern value;
                                function_ = None;
                              };
                          ];
                        uses = Types.no_capabilities;
                        node = pattern.id;
                        origin = pattern.origin;
                      };
                  }))
            origin;
          branch
            (Some
               (Use
                  {
                    place = Emitter.make_local_place local;
                    type_ = Types.bool;
                    origin = pattern.origin;
                  }))
      | _ -> ())
  | Alternatives _ -> raise_bug "alternatives are expanded before they are tested"

and bind ?(owned = false) builder (pattern : Core.pattern) (scrutinee : Tree.place)
    ~scrutinee_origin =
  let bind = bind ~owned ~scrutinee_origin in
  match pattern.kind with
  | Wildcard | Literal _ | Range _ | Equal_to _ -> ()
  | Bind { local; mode; is_var } ->
      let bound =
        Emitter.bind_source ~is_var builder local
          (if owned then Own else mode)
          pattern.type_ pattern.origin
      in
      (match mode with
      | (Read | Mut) when (not owned) && Emitter.reaches builder ->
          Emitter.note_bound_to_place builder bound
      | _ -> ());
      Emitter.emit builder (Basic (Live [ bound ])) pattern.origin;
      Emitter.assign builder (Emitter.make_local_place bound)
        (Operand
           (match mode with
           | Own -> Use { place = scrutinee; type_ = pattern.type_; origin = scrutinee_origin }
           | (Read | Mut) when owned ->
               Use { place = scrutinee; type_ = pattern.type_; origin = scrutinee_origin }
           | Read | Mut ->
               Borrow { place = scrutinee; type_ = pattern.type_; mode; origin = scrutinee_origin }))
        pattern.origin
  | Variant { variant; fields } ->
      List.iter
        (fun (field, inner) ->
          bind builder inner (project scrutinee (Variant_field { variant; field })))
        fields
  | Record fields ->
      List.iter (fun (field, inner) -> bind builder inner (project scrutinee (Field field))) fields
  | Alternatives _ -> raise_bug "alternatives are expanded before they are bound"

and expand_patterns (patterns : Core.pattern list) : Core.pattern list list =
  let rec expand (pattern : Core.pattern) : Core.pattern list =
    match pattern.kind with
    | Alternatives alternatives -> List.concat_map expand alternatives
    | Variant { variant; fields } ->
        List.map
          (fun fields -> { pattern with kind = Variant { variant; fields } })
          (expand_fields fields)
    | Record fields ->
        List.map (fun fields -> { pattern with kind = Record fields }) (expand_fields fields)
    | _ -> [ pattern ]
  and expand_fields fields =
    List.fold_right
      (fun (name, inner) rest ->
        List.concat_map
          (fun inner -> List.map (fun rest -> (name, inner) :: rest) rest)
          (expand inner))
      fields [ [] ]
  in
  List.fold_right
    (fun pattern rest ->
      List.concat_map (fun pattern -> List.map (fun rest -> pattern :: rest) rest) (expand pattern))
    patterns [ [] ]

and lower_statement builder (node : Core.statement) =
  let origin = node.origin in
  Emitter.run_in_statement builder origin (fun () ->
      match node.kind with
      | Let { pattern; value; else_ } -> (
          let scrutinee =
            Emitter.run_extending builder (list_extended_temporaries value) (fun () ->
                lower_scrutinee builder value)
          in
          match (scrutinee, else_) with
          | None, _ -> ()
          | Some place, None ->
              ignore
                (match_patterns ~covers:true builder [ pattern ]
                   [ (place, compute_operand_origin value) ]
                   origin)
          | Some place, Some else_ ->
              let matches, bound =
                Emitter.run_deferring builder (fun () ->
                    match_patterns builder [ pattern ]
                      [ (place, compute_operand_origin value) ]
                      origin)
              in
              Option.iter
                (fun condition ->
                  let then_ = Emitter.build_block builder (fun () -> Some Emitter.unit_value) in
                  let else_ =
                    Emitter.build_block builder (fun () ->
                        ignore
                          (Emitter.run_in_scope builder origin (fun () -> lower_block builder else_));
                        Emitter.jump builder Unreachable origin;
                        None)
                  in
                  ignore
                    (Emitter.hold_choice builder Types.unit origin
                       (Conditional { condition; then_; else_; if_condition = None })))
                matches;
              List.iter (Emitter.register_binding builder) bound)
      | Evaluate value -> ignore (lower_expression builder value)
      | Assign { target; value = written; _ } -> (
          match lower_expression builder written with
          | Some value -> (
              let value =
                if runs_code target then Emitter.hold_operand builder value written.type_ origin
                else value
              in
              let loans =
                match value with
                | Constant _ -> []
                | _ -> [ Emitter.start_loan builder value Read Operand_evaluation origin ]
              in
              let target = lower_place builder target in
              Emitter.end_loans builder loans origin;
              match target with
              | Some target -> Emitter.assign builder target (Operand value) origin
              | None -> ())
          | None -> ())
      | Compound_assign { target; operand = right; bound; value } -> (
          let mode : Types.mode = match right with Place _ -> Read | Value _ -> Own in
          match lower_operand builder mode right with
          | None -> ()
          | Some right_value -> (
              let local =
                Emitter.allocate_local builder
                  (Source { local = bound; mode; is_var = false; is_binding = false })
                  (compute_core_operand_type right) (compute_operand_origin right)
              in
              Emitter.add_source builder bound local;
              Emitter.add_temporary builder local;
              Emitter.emit builder (Basic (Live [ local ])) origin;
              Emitter.assign builder (Emitter.make_local_place local) (Operand right_value) origin;
              let bound_value =
                match right_value with
                | Borrow _ ->
                    Tree.Borrow
                      {
                        place = Emitter.make_local_place local;
                        type_ = compute_core_operand_type right;
                        mode = Read;
                        origin;
                      }
                | _ ->
                    Use
                      {
                        place = Emitter.make_local_place local;
                        type_ = compute_core_operand_type right;
                        origin;
                      }
              in
              let loans =
                [ Emitter.start_loan builder bound_value Read Operand_evaluation origin ]
              in
              let target = lower_place builder target in
              Emitter.end_loans builder loans origin;
              match target with
              | None -> ()
              | Some target -> (
                  let updated =
                    Emitter.with_compound_target builder target (fun () ->
                        lower_expression builder value)
                  in
                  match updated with
                  | Some updated -> Emitter.assign builder target (Operand updated) origin
                  | None -> ())))
      | For { pattern; iteration; clauses; body; mode } -> (
          let loop =
            {
              Tree.clauses = lower_loop_clauses builder clauses;
              schedule = mode;
              origin;
              quantified = None;
            }
          in
          let each ~bind_part =
            let lower_iteration () =
              Emitter.run_in_scope builder origin (fun () ->
                  bind_part ();
                  ignore (lower_block builder body))
            in
            if mode = Concurrent_loop then
              Emitter.run_in_task builder (Tree.Iteration { loop = origin }) lower_iteration
            else lower_iteration ()
          in
          match iteration with
          | Integer_range { start; stop; inclusive } ->
              lower_range_loop builder ~origin ~pattern ~start ~stop ~inclusive
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part)
          | Elements elements ->
              lower_elements_loop builder ~origin ~pattern ~elements
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part)
          | Cursor { cursor; next } ->
              lower_cursor_loop builder ~origin ~pattern ~cursor ~next
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part))
      | While { condition = tested; clauses; body; binds_lent_part } ->
          let loop =
            {
              Tree.clauses = lower_loop_clauses builder clauses;
              schedule = Sequential;
              origin;
              quantified = None;
            }
          in
          let lowered_condition = ref None in
          let condition =
            Emitter.build_block builder (fun () ->
                let lowered =
                  Emitter.run_in_condition_scope builder ~binds_lent_part (fun () ->
                      lower_expression builder tested)
                in
                lowered_condition := Some lowered;
                lowered.value)
          in
          begin match (condition.value, !lowered_condition) with
          | Some _, Some lowered -> (
              let compared =
                match (tested.kind, List.rev condition.statements) with
                | ( Compare _,
                    {
                      kind =
                        Basic
                          (Assign { value = Compare { comparison; left = low; right = high }; _ });
                      _;
                    }
                    :: _ )
                  when Core_walk.has_implicit_measure tested ->
                    Some { Tree.comparison; left = low; right = high }
                | _ -> None
              in
              let body =
                Emitter.build_block builder (fun () ->
                    Emitter.end_scope builder lowered.ended_if_true tested.origin;
                    Emitter.run_in_loop builder (fun () ->
                        ignore
                          (Emitter.run_in_scope ~held:lowered.held_if_true builder origin (fun () ->
                               lower_block builder body)));
                    if Emitter.reaches builder then Some Emitter.unit_value else None)
              in
              let failed =
                Emitter.build_block builder (fun () ->
                    Emitter.end_scope builder lowered.ended_if_false tested.origin;
                    Some Emitter.unit_value)
              in
              Emitter.emit builder
                (While { loop; condition; body; failed = failed.statements; compared })
                origin;
              match condition.value with
              | Some (Constant { value = Boolean true; _ }) when not (holds_break body) ->
                  Emitter.jump builder Unreachable origin
              | _ -> ())
          | _ ->
              List.iter
                (fun (statement : Tree.statement) ->
                  Emitter.emit builder statement.kind statement.origin)
                condition.statements;
              Emitter.mark_unreachable builder
          end
      | Parallel branches | Concurrent branches ->
          let concurrent = match node.kind with Concurrent _ -> true | _ -> false in
          let branches =
            List.mapi
              (fun index (branch : Core.statement) ->
                Emitter.build_block builder (fun () ->
                    if concurrent then
                      Emitter.run_in_task builder
                        (Tree.Branch { block = origin; index })
                        (fun () -> lower_statement builder branch)
                    else lower_statement builder branch;
                    if Emitter.reaches builder then Some Emitter.unit_value else None))
              branches
          in
          Emitter.start_group builder origin origin;
          Emitter.emit builder (Fork { fork = origin; concurrent; branches }) origin;
          Emitter.resume_group builder origin origin;
          if List.exists (fun (branch : Tree.block) -> branch.value = None) branches then
            Emitter.jump builder Unreachable origin
      | Proof proof ->
          Emitter.emit builder
            (Basic (Proof (of_proof ~entry_locals:(Emitter.entry_locals builder) proof)))
            origin
      | Assert { condition = { value; executable = true }; by_bit_vector = false } -> (
          match lower_expression builder value with
          | Some condition -> Emitter.emit builder (Basic (Assert condition)) value.origin
          | None -> ())
      | Assert { condition = { value; executable = true }; by_bit_vector = true } -> (
          let code = Emitter.build_block builder (fun () -> lower_expression builder value) in
          match code.value with
          | Some condition ->
              let names =
                List.sort_uniq compare
                  (List.filter_map
                     (fun (local, _) -> Emitter.find_source builder local)
                     (list_names value))
              in
              Emitter.emit builder (Assert_by_bit_vector { condition; names; code }) value.origin
          | None -> ())
      | Assert { condition = { value; executable = false }; by_bit_vector } ->
          Emitter.emit builder
            (Basic
               (Ghost_assert { condition = lower_attached_formula builder value; by_bit_vector }))
            origin
      | Yield { mode; part = written } -> (
          match lower_yielded builder mode written with
          | Some part -> Emitter.emit builder (Yield { mode; part }) origin
          | None -> ()))

and lower_for_loop ?cursor_type ?(lent = ref None) builder ~origin ~(pattern : Core.pattern)
    ~iteration ~loop ~each =
  let part = Emitter.allocate_local builder Temporary pattern.type_ origin in
  let binding_count = ref 0 in
  let body =
    Emitter.build_block builder (fun () ->
        Emitter.run_in_loop builder (fun () ->
            each (fun () ->
                (match iteration with
                | Tree.Pull { cursor; _ } ->
                    ignore
                      (Emitter.start_loan builder
                         (Borrow
                            {
                              place = cursor;
                              type_ = Option.value ~default:pattern.type_ cursor_type;
                              mode = Read;
                              origin;
                            })
                         Read Loop_body origin)
                | Range _ -> ());
                (match iteration with
                | Range _ ->
                    bind ~owned:true builder pattern (Emitter.make_local_place part)
                      ~scrutinee_origin:pattern.origin
                | Pull _ ->
                    bind builder pattern (Emitter.make_local_place part)
                      ~scrutinee_origin:pattern.origin);
                binding_count := List.length (Emitter.emitted builder)));
        if Emitter.reaches builder then Some Emitter.unit_value else None)
  in
  Emitter.start_group builder origin origin;
  Emitter.emit builder
    (For { loop = loop (); iteration; part; lent = !lent; binding_count = !binding_count; body })
    origin;
  Emitter.resume_group builder origin origin

and lower_range_loop builder ~origin ~pattern ~start:low ~stop:high ~inclusive ~loop ~each =
  match (lower_expression builder low, lower_expression builder high) with
  | Some start, Some stop ->
      let start = Emitter.hold_operand builder start low.type_ origin
      and stop = Emitter.hold_operand builder stop high.type_ origin in
      lower_for_loop builder ~origin ~pattern
        ~iteration:(Range { start; stop; inclusive })
        ~loop ~each
  | _ -> ()

and lower_elements_loop builder ~origin ~(pattern : Core.pattern) ~(elements : Core.elements) ~loop
    ~each =
  let { Core.count; position; element } = elements in
  let counted =
    Emitter.build_block builder (fun () ->
        Option.map
          (fun stop -> Emitter.hold_operand builder stop count.type_ origin)
          (lower_expression builder count))
  in
  match (counted.value, element) with
  | Some stop, Lent lending ->
      let start = Tree.Constant { value = Integer Z.zero; type_ = count.type_ } in
      let lent_part = ref None in
      lower_for_loop ~lent:lent_part builder ~origin ~pattern:position
        ~iteration:(Range { start; stop; inclusive = false })
        ~loop
        ~each:(fun bind_position ->
          each (fun () ->
              bind_position ();
              Option.iter
                (fun (part : Tree.place) ->
                  (match part.root with
                  | Local element -> (
                      match find_lent_place builder element with
                      | Some collection ->
                          lent_part := Some { element; collection; count = counted }
                      | None -> raise_bug "a loop over elements whose collection no call borrows")
                  | Constant _ | Literal _ -> raise_bug "a loop over elements that a constant lends");
                  bind builder pattern part ~scrutinee_origin:pattern.origin)
                (lower_lent builder lending ~duration:Loop_body)))
  | Some _, _ -> raise_bug "a loop over elements that no call lends"
  | None, _ -> ()

and find_lent_place builder part =
  List.find_map
    (fun (statement : Tree.statement) ->
      match statement.kind with
      | Basic
          (Lend
             {
               part = lent;
               call =
                 {
                   arguments = Passed { value = Borrow { place; _ } | Use { place; _ }; _ } :: _;
                   _;
                 };
             })
        when lent = part ->
          Some (Emitter.borrow_place builder place)
      | _ -> None)
    (Emitter.emitted builder)

and lower_cursor_loop builder ~origin ~pattern ~cursor ~next ~loop ~each =
  match lower_place builder cursor with
  | None -> ()
  | Some place_ ->
      let cursor_type = Core_walk.compute_place_type cursor in
      let cursor = place_ in
      Option.iter
        (fun next ->
          lower_for_loop ~cursor_type builder ~origin ~pattern
            ~iteration:(Pull { cursor; next })
            ~loop ~each)
        (lower_callee builder next)

and lower_quantifier_loop builder (node : Core.expression) (quantifier : Core.quantifier)
    (body : Core.expression) run =
  let origin = node.origin in
  let decides = Emitter.allocate_temporary builder Types.bool origin in
  let quantified = ref None in
  Emitter.assign builder
    (Emitter.make_local_place decides)
    (Operand (Constant { value = Boolean (quantifier = Forall); type_ = Types.bool }))
    origin;
  let make_loop () =
    { Tree.clauses = []; schedule = Sequential; origin; quantified = !quantified }
  in
  run ~loop:make_loop ~each:(fun bind_part ->
      Emitter.run_in_scope builder origin (fun () ->
          bind_part ();
          Option.iter
            (fun holds ->
              quantified := Some { Tree.quantifier; decides };
              Emitter.assign builder (Emitter.make_local_place decides) (Operand holds) origin)
            (lower_expression builder body)));
  Some (Use { place = Emitter.make_local_place decides; type_ = Types.bool; origin })

and lower_quantified builder (node : Core.expression) (quantifier : Core.quantifier)
    (binder : Core.binder) (body : Core.expression) =
  let origin = node.origin in
  let range, value_type =
    match binder with
    | Over_type { type_; _ } -> (Some (Tree.Over_type type_), type_)
    | Over_range { pattern; start; stop; inclusive } ->
        ( Option.map
            (fun (start, stop) -> Tree.Over_range { start; stop; inclusive })
            (evaluate_pair builder start stop),
          pattern.type_ )
    | Over_elements { elements; _ } ->
        ( Option.map
            (fun stop ->
              Tree.Over_range
                {
                  start = Constant { value = Integer Z.zero; type_ = elements.count.type_ };
                  stop;
                  inclusive = false;
                })
            (lower_expression builder elements.count),
          elements.count.type_ )
  in
  let* range = range in
  let parameter, matches =
    match binder with
    | Over_type { local; type_ } ->
        ( Emitter.bind_source builder local Own type_ origin,
          {
            Tree.statements = [];
            value = Some (Constant { value = Boolean true; type_ = Types.bool });
          } )
    | Over_range { pattern; _ } ->
        let parameter = Emitter.allocate_local builder Temporary value_type origin in
        ( parameter,
          Emitter.build_block builder (fun () ->
              match_patterns builder [ pattern ]
                [ (Emitter.make_local_place parameter, pattern.origin) ]
                origin) )
    | Over_elements { pattern; elements = { position; element; _ } } ->
        let parameter = Emitter.allocate_local builder Temporary value_type origin in
        ( parameter,
          Emitter.build_block builder (fun () ->
              bind ~owned:true builder position
                (Emitter.make_local_place parameter)
                ~scrutinee_origin:position.origin;
              match element with
              | Lent lending ->
                  let* part = lower_lent builder lending ~duration:Operand_evaluation in
                  match_patterns builder [ pattern ] [ (part, pattern.origin) ] origin
              | _ -> raise_bug "a quantifier over elements that no call lends") )
  in
  let body = Emitter.build_block builder (fun () -> lower_expression builder body) in
  Emitter.hold builder node.type_ origin
    (Specification (Quantified { quantifier; range; parameter; matches; body }))

and lower_lambda builder (parameters : Core.pattern list) (captures : Core.capture list)
    (body : Core.block) =
  let inner = Emitter.make_lambda_builder builder in
  let capture_locals =
    List.map
      (fun (capture : Core.capture) ->
        let is_binding =
          match
            Option.map
              (Emitter.lookup_local_info builder)
              (Emitter.find_source builder capture.local)
          with
          | Some { kind = Source { is_binding; _ }; _ } -> is_binding
          | _ -> false
        in
        let local =
          Emitter.allocate_local inner
            (Source { local = capture.local; mode = Read; is_var = false; is_binding })
            capture.type_ 0
        in
        Emitter.add_source inner capture.local local;
        local)
      captures
  in
  let parameter_locals =
    List.map
      (fun (pattern : Core.pattern) ->
        match pattern.kind with
        | Bind { local; mode; is_var } ->
            Emitter.bind_source ~is_var inner local mode pattern.type_ pattern.origin
        | _ -> Emitter.allocate_local inner Temporary pattern.type_ pattern.origin)
      parameters
  in
  Emitter.run_in_scope inner 0 (fun () ->
      List.iter2
        (fun (pattern : Core.pattern) local ->
          match pattern.kind with
          | Bind _ -> ()
          | _ ->
              bind inner pattern (Emitter.make_local_place local) ~scrutinee_origin:pattern.origin)
        parameters parameter_locals;
      lower_body inner body ~returns:true);
  let rec compute_unconverted_type (value : Core.expression) =
    match value.kind with
    | Convert { conversion = To_integer; value = inner } -> compute_unconverted_type inner
    | _ -> value.type_
  in
  let body =
    Emitter.finish inner ~parameters:parameter_locals ~captures:capture_locals
      ~is_functional:(Core_walk.is_functional (fun visit -> Core_walk.walk_block visit body))
      ?value_type:(Option.map compute_unconverted_type body.value)
  in
  Emitter.add_lambda builder body

and compute_block_type (body : Core.block) =
  match body.value with Some value -> value.type_ | None -> Types.unit

and of_proof ~entry_locals (written : Core.block) =
  let builder = Emitter.create ~is_specification:true ~entry_locals ~takes_free_locals:true () in
  Emitter.run_in_scope builder 0 (fun () -> lower_body builder written ~returns:true);
  let body = Emitter.finish builder ~parameters:(Emitter.free_locals builder) in
  { body; lambdas = Emitter.lambdas builder }

and lower_free_formula ~entry_locals ~origin ~type_ (build : Emitter.t -> Tree.operand option) =
  let builder = Emitter.create ~is_specification:true ~entry_locals ~takes_free_locals:true () in
  Emitter.build_formula builder ~origin ~type_ (fun () ->
      let value = build builder in
      (Emitter.free_locals builder, value))

and of_specification ~entry_locals (written : Core.expression) =
  lower_free_formula ~entry_locals ~origin:written.origin ~type_:written.type_ (fun builder ->
      lower_expression builder written)

and of_law_statement ~entry_locals (written : Core.block) =
  lower_free_formula ~entry_locals ~origin:0 ~type_:(compute_block_type written) (fun builder ->
      lower_block builder written)

and lower_attached_formula builder (written : Core.expression) =
  of_specification ~entry_locals:(Emitter.entry_locals builder) written

and lower_loop_clauses builder (clauses : Core.loop_clause list) : Tree.loop_clause list =
  let lower_bound : Core.bound -> Tree.bound = function
    | Finite -> Finite
    | Order_of amount -> Order_of (lower_attached_formula builder amount)
    | At_most amount -> At_most (lower_attached_formula builder amount)
    | Exactly amount -> Exactly (lower_attached_formula builder amount)
  in
  List.map
    (function
      | Core.Invariant invariant -> Tree.Invariant (lower_attached_formula builder invariant)
      | Decreases measures -> Decreases (List.map (lower_attached_formula builder) measures)
      | Cost { origin; amortized; resource; bound = written } ->
          Cost { origin; amortized; resource; bound = lower_bound written })
    clauses

let of_expression (written : Core.expression) =
  let builder = Emitter.create ~entry_locals:[] () in
  Emitter.run_in_scope builder written.origin (fun () ->
      Emitter.run_in_statement builder written.origin (fun () ->
          Option.iter
            (fun value -> Emitter.return_ builder (Some value) written.origin)
            (lower_expression builder written)));
  let body = Emitter.finish builder ~parameters:[] in
  { Tree.body; lambdas = Emitter.lambdas builder }

let of_clause ?(is_executable = false) ~(parameters : Core.parameter list)
    (written : Core.expression) =
  let builder =
    Emitter.create ~is_specification:(not is_executable)
      ~entry_locals:(List.map (fun (parameter : Core.parameter) -> parameter.local) parameters)
      ()
  in
  let locals =
    List.map
      (fun (parameter : Core.parameter) ->
        Emitter.bind_source builder parameter.local parameter.mode parameter.type_ 0)
      parameters
  in
  Emitter.build_formula builder ~origin:written.origin ~type_:written.type_ (fun () ->
      (locals, lower_expression builder written))

let of_definition ~is_specification (definition : Core.definition) =
  let code =
    match definition with
    | Function { parameters; body = Some body; _ } -> Some (parameters, body, true)
    | Test (Some body) -> Some ([], body, false)
    | Law_proof { parameters; body = Some body } -> Some (parameters, body, false)
    | Function { body = None; _ }
    | Test None
    | Law_proof { body = None; _ }
    | Type _ | Trait _ | Constant _ | Empty ->
        None
  in
  Option.map
    (fun ((parameters : Core.parameter list), (body : Core.block), returns) ->
      let builder =
        Emitter.create ~is_specification
          ~entry_locals:(List.map (fun (parameter : Core.parameter) -> parameter.local) parameters)
          ()
      in
      let locals =
        List.map
          (fun (parameter : Core.parameter) ->
            Emitter.bind_source builder parameter.local parameter.mode parameter.type_ 0)
          parameters
      in
      Emitter.run_in_scope builder 0 (fun () -> lower_body builder body ~returns);
      { Tree.body = Emitter.finish builder ~parameters:locals; lambdas = Emitter.lambdas builder })
    code

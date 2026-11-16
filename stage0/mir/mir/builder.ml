let bug format = Compiler_bug.bug ~stage:"MIR" format

let rec holds_break (block : Tree.block) =
  List.exists
    (fun (statement : Tree.statement) ->
      match statement.kind with
      | Jump Break -> true
      | While _ | For _ -> false
      | _ -> List.exists holds_break (Walk.nested_blocks statement))
    block.statements

let project (place : Tree.place) projection =
  { place with projections = place.projections @ [ projection ] }

let ( let* ) = Option.bind

let core_operand_type : Core.operand -> Types.ty = function
  | Place place -> Core_walk.place_type place
  | Value value -> value.type_

let operand_origin : Core.operand -> Core.origin = function
  | Place place -> Core_walk.place_origin place
  | Value value -> value.origin

module In_order = struct
  type 'value t = {
    slots : int;
    origin : Core.origin option;
    evaluate : count:int -> index:int -> loans:int list ref -> 'value option;
  }

  let pure value =
    { slots = 0; origin = None; evaluate = (fun ~count:_ ~index:_ ~loans:_ -> Some value) }

  let operand_with builder evaluate type_ origin =
    {
      slots = 1;
      origin = Some origin;
      evaluate =
        (fun ~count ~index ~loans ->
          let* value, extra = evaluate () in
          if count > 1 then begin
            let value = Emitter.held builder value type_ origin in
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

  let operand builder evaluate type_ origin =
    map fst
      (operand_with builder
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

let rec field_path (place : Tree.place) = function
  | [] -> place
  | field :: rest -> field_path (project place (Field field)) rest

let rec extended_temporaries (value : Core.operand) =
  match value with Place base -> extended_base base | Value value -> extended_by value

and extended_by (value : Core.expression) =
  match value.kind with
  | Slice { base; _ } -> extended_base base
  | Construct { fields; _ } ->
      List.concat_map
        (fun (_, field) -> Option.fold ~none:[] ~some:extended_temporaries field)
        fields
  | Record_update { updates; _ } -> List.concat_map (fun (_, update) -> extended_by update) updates
  | Collection_literal { elements; construction = Array } -> List.concat_map extended_by elements
  | _ -> []

and extended_base (base : Core.place) =
  match base with
  | Temporary written -> written.id :: extended_by written
  | Field { base; _ } -> extended_base base
  | Local _ | Constant _ | Lent _ -> []

let is_functional walk =
  let fine = ref true in
  let rec visit =
    {
      Core_walk.ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Return _ | Break | Continue | Todo | Echo _ | Provide _ | Unreachable -> fine := false
          | _ when diverges node.type_ -> fine := false
          | Call { arguments; _ } ->
              if
                List.exists
                  (function
                    | Core.Passed { mode = Types.Mut; _ } -> true
                    | Core.Passed _ | Core.Default -> false)
                  arguments
              then fine := false;
              Core_walk.expression_children visit node
          | _ -> Core_walk.expression_children visit node);
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Let { pattern; else_ = None; _ } when not (binds_variable pattern) ->
              Core_walk.statement_children visit node
          | Evaluate _ -> Core_walk.statement_children visit node
          | _ -> fine := false);
      pattern = (fun node -> Core_walk.pattern_children visit node);
    }
  and binds_variable (pattern : Core.pattern) =
    let child_binds = ref false in
    Core_walk.pattern_children
      {
        Core_walk.ignore_all with
        pattern = (fun inner -> if binds_variable inner then child_binds := true);
      }
      pattern;
    !child_binds || match pattern.kind with Bind { is_var; _ } -> is_var | _ -> false
  in
  walk visit;
  !fine

let names_of (written : Core.expression) =
  let names = ref [] in
  Core_walk.expression
    {
      Core_walk.ignore_all with
      place =
        (function Local { local; origin; _ } -> names := (local, origin) :: !names | _ -> ());
    }
    written;
  List.rev !names

let literal_place text type_ = { Tree.root = Literal { text; type_ }; projections = [] }

let read_literal text type_ origin =
  Tree.Borrow { place = literal_place text type_; type_; mode = Read; origin }

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

let rec expression builder (node : Core.expression) : Tree.operand option =
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
        let* call = call_of builder called ~node:node.id ~origin:node.origin in
        let local = Emitter.temporary builder node.type_ origin in
        Emitter.emit builder
          (Basic (Template { destination = Emitter.at local; literals; call }))
          origin;
        Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin = node.origin })
    | Template _ -> bug "a tagged template whose value is not a call"
    | Use place_ ->
        let* place_ = place builder place_ in
        Some (Tree.Use { place = place_; type_ = node.type_; origin = node.origin })
    | Copy copied ->
        let* copied = operand builder Read copied in
        hold (Copy copied)
    | Function_value _ | Lambda _ ->
        Option.map fst (function_expression builder node ~is_argument:false)
    | Value_parameter parameter -> hold (Value_parameter parameter)
    | Construct { variant; fields } ->
        let* fields = construct_fields builder fields in
        hold (Construct { variant; fields })
    | Collection_literal { elements; construction = Array } ->
        let* elements = operands builder elements in
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
        let local = Emitter.temporary builder node.type_ origin in
        Emitter.assign builder (Emitter.at local) (Operand base_value) origin;
        List.iter
          (fun (fields, (written : Core.expression), value) ->
            Emitter.assign builder
              (field_path (Emitter.at local) fields)
              (Operand value) written.origin)
          update_values;
        Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin = node.origin })
    | Slice { base; callee; bounds } ->
        let* callee = callee_of builder callee in
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
            arguments =
              Passed { mode = Read; value = receiver; mode_keyword = None; function_ = None }
              :: bounds;
            uses = Types.no_capabilities;
            node = node.id;
            origin = node.origin;
          }
        in
        let local = Emitter.temporary builder node.type_ origin in
        Emitter.emit builder
          (Basic
             (Slice
                {
                  destination = Emitter.at local;
                  base = Emitter.borrowed_place builder base_place;
                  base_type = Core_walk.place_type base;
                  call;
                }))
          origin;
        Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin = node.origin })
    | Call called -> call_value builder node called
    | Operator { operation; arguments } ->
        let* operands = operands builder arguments in
        let type_arguments =
          List.map (fun (argument : Core.expression) -> Types.Type argument.type_) arguments
        in
        hold (Operation { operation; type_arguments; operands })
    | Compare { comparison; left; right } ->
        let* left, right = evaluate_pair builder left right in
        hold (Compare { comparison; left; right })
    | Not inner ->
        let* inner = expression builder inner in
        hold (Not inner)
    | And _ | Or _ | Implies _ | Matches _ -> truth builder node
    | Convert { conversion = Widen; value = converted } when is_function_expression converted ->
        Option.map fst (function_expression builder node ~is_argument:false)
    | Convert { conversion; value = converted } ->
        let* value = expression builder converted in
        hold (Convert { conversion; value; converts_function_expression = false })
    | To_any { value; trait; evidence } ->
        let* value = expression builder value in
        hold (To_any { value; trait; evidence })
    | If { condition = tested; then_; else_; binds_lent_part } ->
        let condition, on_true, on_false, held =
          Emitter.in_condition_scope builder
            ~lends:(if binds_lent_part then For_block else For_condition)
            (fun () -> expression builder tested)
        in
        let* condition = condition in
        let result = value_local builder node in
        let arm ?held ended (body : Core.block option) =
          Emitter.block_of builder (fun () ->
              Emitter.end_scope builder ended tested.origin;
              Emitter.in_scope ?held builder origin (fun () ->
                  match (Option.map (block builder) body, result) with
                  | Some (Some value), Some local ->
                      Emitter.assign builder (Emitter.at local) (Operand value) origin;
                      Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin })
                  | Some None, _ -> None
                  | (Some (Some _) | None), _ -> Some Emitter.unit_value))
        in
        let then_ = arm ~held on_true (Some then_) in
        let else_ = arm on_false else_ in
        chosen builder node [ then_; else_ ]
          (Tree.Conditional { condition; then_; else_; if_condition = Some tested.origin })
    | Match { scrutinees; arms } -> match_ builder node scrutinees arms
    | Block inner -> Emitter.in_value_scope builder origin (fun () -> block builder inner)
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
                      (In_order.operand builder
                         (fun () -> operand builder implementation.mode implementation.value)
                         implementation.type_ implementation.origin))
                  implementations))
        in
        Emitter.emit builder
          (Basic (Provide { provided; can_use_tasks = Core_walk.can_use_tasks body }))
          origin;
        Emitter.in_value_scope ~provides:true builder origin (fun () ->
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
            block builder body)
    | Return returned ->
        (match returned with
        | None -> Emitter.return_ builder None origin
        | Some returned ->
            Option.iter
              (fun value -> Emitter.return_ builder (Some value) origin)
              (expression builder returned));
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
        let* value = expression builder inner in
        let local = Emitter.temporary builder inner.type_ origin in
        Emitter.assign builder (Emitter.at local) (Operand value) origin;
        Emitter.emit builder
          (Basic
             (Echo (Borrow { place = Emitter.at local; type_ = inner.type_; mode = Read; origin })))
          origin;
        Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin = node.origin })
    | Current_target -> (
        match Emitter.compound_target builder with
        | Some target -> Some (Take { place = target; type_ = node.type_; origin = node.origin })
        | None -> bug "the old value of a target outside a compound assignment")
    | Quantified { quantifier; binder; body } when Emitter.is_specification builder ->
        quantified builder node quantifier binder body
    | Quantified { quantifier; binder = Over_range { pattern; start; stop; inclusive }; body } ->
        quantifier_loop builder node quantifier body (fun ~loop ~each ->
            range_loop builder ~origin ~pattern ~start ~stop ~inclusive ~loop ~each)
    | Quantified { quantifier; binder = Over_elements { pattern; elements }; body } ->
        quantifier_loop builder node quantifier body (fun ~loop ~each ->
            elements_loop builder ~origin ~pattern ~elements ~loop ~each)
    | Collection_literal { elements; construction = Specification_only } ->
        let* elements = operands builder elements in
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
    | Old inner -> Emitter.in_old builder (fun () -> expression builder inner)
    | Identical (first, second) ->
        let* first, second = evaluate_pair builder first second in
        hold (Specification (Identical (first, second)))
    | Specification_function { function_; arguments } ->
        let rec unconverted (argument : Core.expression) =
          match argument.kind with
          | Convert { conversion = To_integer; value } -> unconverted value
          | _ -> argument.type_
        in
        let unconverted = List.map unconverted arguments in
        let* arguments = operands builder arguments in
        hold (Specification (Applied { function_; arguments; unconverted }))
    | Method_time callee ->
        let* callee = callee_of builder callee in
        hold (Specification (Method_time callee))
    | Quantified _ -> bug "a quantifier over a type or a collection in code that runs"

and plan_expression builder (node : Core.expression) =
  In_order.operand builder (fun () -> expression builder node) node.type_ node.origin

and plan_operand builder mode (passed : Core.operand) =
  In_order.operand builder
    (fun () -> operand builder mode passed)
    (core_operand_type passed) (operand_origin passed)

and operands builder nodes =
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
                  (In_order.operand builder
                     (fun () ->
                       match field with
                       | Place _ ->
                           bug
                             "a constructor field that is a place, in a construct that no lending \
                              method lends"
                       | Value value -> expression builder value)
                     (core_operand_type field) (operand_origin field)))
          fields))

and yielded builder (mode : Types.mode) (part : Core.operand) : Tree.yielded option =
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
  | _ -> Option.map (fun value -> Tree.Part value) (operand builder mode part)

and operand builder (mode : Types.mode) (passed : Core.operand) =
  match passed with
  | Place written ->
      let* passed = place builder written in
      Some (borrow written passed mode)
  | Value value -> expression builder value

and borrow (written : Core.place) (place : Tree.place) mode =
  Borrow
    { place; type_ = Core_walk.place_type written; mode; origin = Core_walk.place_origin written }

and plan_borrow builder (written : Core.place) =
  In_order.operand_with builder
    (fun () ->
      let* place = place builder written in
      Some (borrow written place Read, place))
    (Core_walk.place_type written) (Core_walk.place_origin written)

and place builder (written : Core.place) : Tree.place option =
  if not (Emitter.reaches builder) then None
  else
    match written with
    | Local { local; type_; origin } when Emitter.reads_entry builder local ->
        let entry = Emitter.temporary builder type_ origin in
        Emitter.assign builder (Emitter.at entry)
          (Specification (Entry (Emitter.free_source builder local ~type_ ~origin)))
          origin;
        Some (Emitter.at entry)
    | Local { local; type_; origin } ->
        Some (Emitter.at (Emitter.free_source builder local ~type_ ~origin))
    | Constant { path; _ } -> Some { root = Constant path; projections = [] }
    | Field { base; field; _ } ->
        let* base = place builder base in
        Some (project base (Field field))
    | Lent lending -> lent builder lending ~duration:Tree.Rest_of_statement
    | Temporary { kind = String text; type_; _ } -> Some (literal_place text type_)
    | Temporary written ->
        let* value = expression builder written in
        let local = Emitter.place_temporary builder ~node:written.id written.type_ written.origin in
        Emitter.assign builder (Emitter.at local) (Operand value) written.origin;
        Some (Emitter.at local)

and lent builder (lending : Core.expression) ~duration : Tree.place option =
  match lending.kind with
  | Call ({ lends = Some mode; _ } as called) ->
      let* call = call_of builder called ~node:lending.id ~origin:lending.origin in
      let part = Emitter.new_local builder (Lent mode) lending.type_ lending.origin in
      Emitter.add_temporary builder part;
      Emitter.emit builder (Basic (Lend { part; call })) lending.origin;
      (match call.arguments with
      | Passed { mode; value = Borrow _ as receiver; _ } :: _ ->
          ignore
            (Emitter.start_loan builder receiver
               (if mode = Mut then Mut else Read)
               duration lending.origin)
      | _ -> ());
      Some (Emitter.at part)
  | Call _ -> bug "a lent place whose call does not lend"
  | _ -> bug "a lent place that is not a call"

and function_expression builder (node : Core.expression) ~is_argument :
    (Tree.operand * Tree.function_argument) option =
  let origin = node.origin in
  let hold value = Emitter.hold builder node.type_ origin value in
  match node.kind with
  | Function_value { path; type_arguments } ->
      let* value = hold (Function_value { path; type_arguments; is_argument }) in
      Some (value, Tree.Function_reference { path; origin })
  | Lambda { parameters; captures; body; _ } ->
      let index = lambda builder parameters captures body in
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
                         Emitter.at
                           (Emitter.free_source builder capture.local ~type_:capture.type_ ~origin);
                     })
                   captures;
             })
      in
      Some (value, Tree.Lambda_expression { body = index; origin; type_ = node.type_ })
  | Convert { conversion = Widen as conversion; value = converted } ->
      let* value, function_ = function_expression builder converted ~is_argument in
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
  | _ -> bug "a function expression that is no function and no lambda"

and callee_of builder (callee : Core.callee) : Tree.callee option =
  Core_walk.traverse_indirect (operand builder Read) callee

and call_of builder (called : Core.call) ~node ~origin : Tree.call option =
  let* callee = callee_of builder called.callee in
  let* arguments =
    In_order.run builder (In_order.all (List.map (plan_argument builder) called.arguments))
  in
  Some { Tree.callee; arguments; uses = called.uses; node; origin }

and plan_argument builder (argument : Core.argument) =
  match argument with
  | Default -> In_order.pure Tree.Default
  | Passed { mode; value; mode_keyword } ->
      In_order.map
        (fun (value, function_) -> Tree.Passed { mode; value; mode_keyword; function_ })
        (In_order.operand_with builder
           (fun () ->
             match value with
             | Value written when is_function_expression written ->
                 Option.map
                   (fun (passed, function_) -> (passed, Some function_))
                   (function_expression builder written ~is_argument:true)
             | Place _ | Value _ ->
                 Option.map (fun passed -> (passed, None)) (operand builder mode value))
           (core_operand_type value) (operand_origin value))

and call_value builder (node : Core.expression) (called : Core.call) =
  let origin = node.origin in
  match called.callee with
  | Intrinsic { operation; type_arguments } when Intrinsic.primitive operation ->
      let* operands =
        In_order.run builder
          (In_order.all
             (List.map
                (function
                  | Core.Passed { value; mode; _ } -> plan_operand builder mode value
                  | Default -> bug "a primitive operation with a default argument")
                called.arguments))
      in
      Emitter.hold builder node.type_ origin (Operation { operation; type_arguments; operands })
  | _ ->
      let* call = call_of builder called ~node:node.id ~origin:node.origin in
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
        let local = Emitter.temporary builder node.type_ origin in
        Emitter.emit builder (Basic (Call { destination = Some (Emitter.at local); call })) origin;
        Some (Use { place = Emitter.at local; type_ = node.type_; origin = node.origin })

and chosen builder (node : Core.expression) (blocks : Tree.block list) choice =
  let type_ = if diverges node.type_ then Types.unit else node.type_ in
  let held = Emitter.hold_choice builder type_ node.origin choice in
  if List.exists (fun (block : Tree.block) -> block.value <> None) blocks then held
  else begin
    Emitter.mark_unreachable builder;
    None
  end

and truth builder (node : Core.expression) : Tree.operand option =
  let connective connective (left : Core.expression) (right : Core.expression) =
    let* left = expression builder left in
    let right = Emitter.block_of builder (fun () -> expression builder right) in
    Emitter.hold_choice builder node.type_ node.origin (Connective { connective; left; right })
  in
  match node.kind with
  | And (left, right) -> connective And left right
  | Or (left, right) -> connective Or left right
  | Implies (left, right) -> connective Implies left right
  | Matches { value; pattern } ->
      let* scrutinee = scrutinee builder value in
      Emitter.binding_to_statement builder (fun () ->
          match_patterns builder [ pattern ] [ scrutinee ] node.origin)
  | _ -> bug "a condition that is no short-circuit operator and no `is`"

and pattern_tests ?(matched = ignore) builder (patterns : Core.pattern list) places :
    Tree.operand option =
  let tested = ref [] in
  let branch_on value origin =
    match value with
    | Some left when Emitter.reaches builder ->
        tested := (left, Emitter.suspend_block builder, origin) :: !tested
    | _ -> ()
  in
  List.iter2 (fun pattern place -> test builder pattern place ~branch_on) patterns places;
  matched ();
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

and match_patterns ?(covers = false) builder (patterns : Core.pattern list) places origin :
    Tree.operand option =
  let matched patterns () = List.iter2 (bind builder) patterns places in
  let rec any = function
    | [] -> bug "a pattern with no alternative"
    | [ patterns ] when covers ->
        matched patterns ();
        Some (Tree.Constant { value = Boolean true; type_ = Types.bool })
    | [ patterns ] -> pattern_tests builder patterns places ~matched:(matched patterns)
    | patterns :: later ->
        let* left = pattern_tests builder patterns places ~matched:(matched patterns) in
        let right = Emitter.block_of builder (fun () -> any later) in
        Emitter.hold_choice builder Types.bool origin (Connective { connective = Or; left; right })
  in
  any (expansions patterns)

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
  let places =
    List.map
      (fun ((scrutinee : Core.operand), value) ->
        scrutinee_place builder value (core_operand_type scrutinee) (operand_origin scrutinee))
      scrutinee_values
  in
  let result = value_local builder node in
  let left_by_arm_before = ref [] in
  let case (arm : Core.arm) : Tree.case =
    Emitter.in_arm_scope builder @@ fun scope ->
    let tests =
      Emitter.block_of builder (fun () ->
          List.iter
            (fun (ended : Tree.statement) -> Emitter.emit builder ended.kind ended.origin)
            !left_by_arm_before;
          match_patterns builder arm.patterns places arm.origin)
    in
    let guard =
      Option.map
        (fun (guard : Core.expression) ->
          Emitter.block_of builder (fun () ->
              let loans =
                List.filter_map
                  (fun value ->
                    match value with
                    | Tree.Constant _ -> None
                    | _ ->
                        Some (Emitter.start_loan builder value Read Operand_evaluation arm.origin))
                  evaluated
              in
              let holds, ended, _, _ =
                Emitter.in_condition_scope ~lends:For_statement builder (fun () ->
                    expression builder guard)
              in
              let holds =
                Option.map
                  (fun value ->
                    let local = Emitter.temporary builder Types.bool guard.origin in
                    Emitter.assign builder (Emitter.at local) (Operand value) guard.origin;
                    Tree.Use { place = Emitter.at local; type_ = Types.bool; origin = guard.origin })
                  holds
              in
              Emitter.end_scope builder ended guard.origin;
              Emitter.end_loans builder loans arm.origin;
              holds))
        arm.guard
    in
    let value =
      Emitter.block_of builder (fun () ->
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
            match (block builder arm.body, result) with
            | Some value, Some local ->
                Emitter.assign builder (Emitter.at local) (Operand value) arm.origin;
                Some (Tree.Use { place = Emitter.at local; type_ = node.type_; origin })
            | Some _, None -> Some Emitter.unit_value
            | None, _ -> None
          in
          Emitter.end_scope builder scope arm.origin;
          value)
    in
    left_by_arm_before := Emitter.dead_in scope arm.origin;
    { Tree.tests; guard; value }
  in
  let cases = List.map case arms in
  chosen builder node (List.map (fun (case : Tree.case) -> case.value) cases) (Cases cases)

and value_local builder (node : Core.expression) =
  if is_unit node.type_ || diverges node.type_ then None
  else Some (Emitter.temporary builder node.type_ node.origin)

and block builder (body : Core.block) : Tree.operand option =
  List.iter (statement builder) body.statements;
  match body.value with
  | Some value -> expression builder value
  | None -> if Emitter.reaches builder then Some Emitter.unit_value else None

and scrutinee builder (matched : Core.operand) : Tree.place option =
  match matched with
  | Place written -> place builder written
  | Value value ->
      let* value = expression builder value in
      let local = Emitter.temporary builder (core_operand_type matched) (operand_origin matched) in
      Emitter.assign builder (Emitter.at local) (Operand value) (operand_origin matched);
      Some (Emitter.at local)

and scrutinee_place builder (value : Tree.operand) type_ origin : Tree.place =
  match value with
  | Borrow { place; _ } -> place
  | Use { place = { root = Local local; projections = [] } as place; _ }
    when (Emitter.local_info builder local).kind = Temporary ->
      place
  | Use _ | Take _ | Constant _ ->
      let local = Emitter.temporary builder type_ origin in
      Emitter.assign builder (Emitter.at local) (Operand value) origin;
      Emitter.at local

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
      match callee_of builder equal with
      | Some callee when Emitter.reaches builder ->
          let local = Emitter.temporary builder Types.bool origin in
          Emitter.emit builder
            (Basic
               (Call
                  {
                    destination = Some (Emitter.at local);
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
                                mode_keyword = None;
                                function_ = None;
                              };
                            Passed
                              {
                                mode = Read;
                                value = lower_pattern_constant pattern value;
                                mode_keyword = None;
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
            (Some (Use { place = Emitter.at local; type_ = Types.bool; origin = pattern.origin }))
      | _ -> ())
  | Alternatives _ -> bug "alternatives are expanded before they are tested"

and bind ?(owned = false) builder (pattern : Core.pattern) (scrutinee : Tree.place) =
  let bind = bind ~owned in
  match pattern.kind with
  | Wildcard | Literal _ | Range _ | Equal_to _ -> ()
  | Bind { local; mode; name; is_var } ->
      let bound =
        Emitter.bind_source ~name ~is_var builder local
          (if owned then Own else mode)
          pattern.type_ pattern.origin
      in
      (match mode with
      | (Read | Mut) when (not owned) && Emitter.reaches builder ->
          Emitter.note_bound_to_place builder bound
      | _ -> ());
      Emitter.emit builder (Basic (Live [ bound ])) pattern.origin;
      Emitter.assign builder (Emitter.at bound)
        (Operand
           (match mode with
           | Own -> Use { place = scrutinee; type_ = pattern.type_; origin = pattern.origin }
           | (Read | Mut) when owned ->
               Use { place = scrutinee; type_ = pattern.type_; origin = pattern.origin }
           | Read | Mut ->
               Borrow { place = scrutinee; type_ = pattern.type_; mode; origin = pattern.origin }))
        pattern.origin
  | Variant { variant; fields } ->
      List.iter
        (fun (field, inner) ->
          bind builder inner (project scrutinee (Variant_field { variant; field })))
        fields
  | Record fields ->
      List.iter (fun (field, inner) -> bind builder inner (project scrutinee (Field field))) fields
  | Alternatives _ -> bug "alternatives are expanded before they are bound"

and expansions (patterns : Core.pattern list) : Core.pattern list list =
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

and statement builder (node : Core.statement) =
  let origin = node.origin in
  Emitter.in_statement builder origin (fun () ->
      match node.kind with
      | Let { pattern; value; else_ } -> (
          let scrutinee =
            Emitter.extending builder (extended_temporaries value) (fun () ->
                scrutinee builder value)
          in
          match (scrutinee, else_) with
          | None, _ -> ()
          | Some scrutinee, None ->
              ignore (match_patterns ~covers:true builder [ pattern ] [ scrutinee ] origin)
          | Some scrutinee, Some else_ ->
              let matches, bound =
                Emitter.deferring builder (fun () ->
                    match_patterns builder [ pattern ] [ scrutinee ] origin)
              in
              Option.iter
                (fun condition ->
                  let then_ = Emitter.block_of builder (fun () -> Some Emitter.unit_value) in
                  let else_ =
                    Emitter.block_of builder (fun () ->
                        ignore (Emitter.in_scope builder origin (fun () -> block builder else_));
                        Emitter.jump builder Unreachable origin;
                        None)
                  in
                  ignore
                    (Emitter.hold_choice builder Types.unit origin
                       (Conditional { condition; then_; else_; if_condition = None })))
                matches;
              List.iter (Emitter.register_binding builder) bound)
      | Evaluate value -> ignore (expression builder value)
      | Assign { target; value = written; _ } -> (
          match expression builder written with
          | Some value -> (
              let value =
                if runs_code target then Emitter.held builder value written.type_ origin else value
              in
              let loans =
                match value with
                | Constant _ -> []
                | _ -> [ Emitter.start_loan builder value Read Operand_evaluation origin ]
              in
              let target = place builder target in
              Emitter.end_loans builder loans origin;
              match target with
              | Some target -> Emitter.assign builder target (Operand value) origin
              | None -> ())
          | None -> ())
      | Compound_assign { target; operand = right; bound; value } -> (
          let mode : Types.mode = match right with Place _ -> Read | Value _ -> Own in
          match operand builder mode right with
          | None -> ()
          | Some right_value -> (
              let local =
                Emitter.new_local builder
                  (Source { local = bound; mode; name = None; is_var = false })
                  (core_operand_type right) origin
              in
              Emitter.add_source builder bound local;
              Emitter.add_temporary builder local;
              Emitter.emit builder (Basic (Live [ local ])) origin;
              Emitter.assign builder (Emitter.at local) (Operand right_value) origin;
              let bound_value =
                match right_value with
                | Borrow _ ->
                    Tree.Borrow
                      {
                        place = Emitter.at local;
                        type_ = core_operand_type right;
                        mode = Read;
                        origin;
                      }
                | _ -> Use { place = Emitter.at local; type_ = core_operand_type right; origin }
              in
              let loans =
                [ Emitter.start_loan builder bound_value Read Operand_evaluation origin ]
              in
              let target = place builder target in
              Emitter.end_loans builder loans origin;
              match target with
              | None -> ()
              | Some target -> (
                  let updated =
                    Emitter.with_compound_target builder target (fun () -> expression builder value)
                  in
                  match updated with
                  | Some updated -> Emitter.assign builder target (Operand updated) origin
                  | None -> ())))
      | For { pattern; iteration; clauses; body; mode } -> (
          let loop =
            {
              Tree.clauses = loop_clauses builder clauses;
              schedule = mode;
              origin;
              quantified = None;
            }
          in
          let each ~bind_part =
            let iteration () =
              Emitter.in_scope builder origin (fun () ->
                  bind_part ();
                  ignore (block builder body))
            in
            if mode = Concurrent_loop then
              Emitter.in_task builder (Tree.Iteration { loop = origin }) iteration
            else iteration ()
          in
          match iteration with
          | Integer_range { start; stop; inclusive } ->
              range_loop builder ~origin ~pattern ~start ~stop ~inclusive
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part)
          | Elements elements ->
              elements_loop builder ~origin ~pattern ~elements
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part)
          | Cursor { cursor; next } ->
              cursor_loop builder ~origin ~pattern ~cursor ~next
                ~loop:(fun () -> loop)
                ~each:(fun bind_part -> each ~bind_part))
      | While { condition = tested; clauses; body; binds_lent_part } ->
          let loop =
            {
              Tree.clauses = loop_clauses builder clauses;
              schedule = Sequential;
              origin;
              quantified = None;
            }
          in
          let ends = ref None in
          let condition =
            Emitter.block_of builder (fun () ->
                let value, on_true, on_false, held =
                  Emitter.in_condition_scope builder
                    ~lends:(if binds_lent_part then For_block else For_condition)
                    (fun () -> expression builder tested)
                in
                ends := Some (on_true, on_false, held);
                value)
          in
          begin match (condition.value, !ends) with
          | Some _, Some (on_true, on_false, held) -> (
              let compared =
                match (tested.kind, List.rev condition.statements) with
                | ( Compare { left; right; _ },
                    {
                      kind =
                        Basic
                          (Assign { value = Compare { comparison; left = low; right = high }; _ });
                      _;
                    }
                    :: _ )
                  when is_functional (fun visit -> Core_walk.expression visit left)
                       && is_functional (fun visit -> Core_walk.expression visit right) ->
                    Some { Tree.comparison; left = low; right = high }
                | _ -> None
              in
              let body =
                Emitter.block_of builder (fun () ->
                    Emitter.end_scope builder on_true tested.origin;
                    Emitter.looping builder (fun () ->
                        ignore
                          (Emitter.in_scope ~held builder origin (fun () -> block builder body)));
                    if Emitter.reaches builder then Some Emitter.unit_value else None)
              in
              let failed =
                Emitter.block_of builder (fun () ->
                    Emitter.end_scope builder on_false tested.origin;
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
                Emitter.block_of builder (fun () ->
                    if concurrent then
                      Emitter.in_task builder
                        (Tree.Branch { block = origin; index })
                        (fun () -> statement builder branch)
                    else statement builder branch;
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
          match expression builder value with
          | Some condition -> Emitter.emit builder (Basic (Assert condition)) origin
          | None -> ())
      | Assert { condition = { value; executable = true }; by_bit_vector = true } -> (
          let code = Emitter.block_of builder (fun () -> expression builder value) in
          match code.value with
          | Some condition ->
              let names =
                List.sort_uniq compare
                  (List.filter_map
                     (fun (local, _) -> Emitter.source builder local)
                     (names_of value))
              in
              Emitter.emit builder (Assert_by_bit_vector { condition; names; code }) origin
          | None -> ())
      | Assert { condition = { value; executable = false }; by_bit_vector } ->
          Emitter.emit builder
            (Basic (Ghost_assert { condition = attached builder value; by_bit_vector }))
            origin
      | Yield { mode; part = written } -> (
          match yielded builder mode written with
          | Some part -> Emitter.emit builder (Yield { mode; part }) origin
          | None -> ()))

and for_loop ?cursor_type ?(lent = ref None) builder ~origin ~(pattern : Core.pattern) ~iteration
    ~loop ~each =
  let part = Emitter.new_local builder Temporary pattern.type_ origin in
  let binding_count = ref 0 in
  let body =
    Emitter.block_of builder (fun () ->
        Emitter.looping builder (fun () ->
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
                | Range _ -> bind ~owned:true builder pattern (Emitter.at part)
                | Pull _ -> bind builder pattern (Emitter.at part));
                binding_count := List.length (Emitter.emitted builder)));
        if Emitter.reaches builder then Some Emitter.unit_value else None)
  in
  Emitter.start_group builder origin origin;
  Emitter.emit builder
    (For { loop = loop (); iteration; part; lent = !lent; binding_count = !binding_count; body })
    origin;
  Emitter.resume_group builder origin origin

and range_loop builder ~origin ~pattern ~start:low ~stop:high ~inclusive ~loop ~each =
  match (expression builder low, expression builder high) with
  | Some start, Some stop ->
      let start = Emitter.held builder start low.type_ origin
      and stop = Emitter.held builder stop high.type_ origin in
      for_loop builder ~origin ~pattern ~iteration:(Range { start; stop; inclusive }) ~loop ~each
  | _ -> ()

and elements_loop builder ~origin ~(pattern : Core.pattern) ~(elements : Core.elements) ~loop ~each
    =
  let { Core.count; position; element } = elements in
  let counted =
    Emitter.block_of builder (fun () ->
        Option.map
          (fun stop -> Emitter.held builder stop count.type_ origin)
          (expression builder count))
  in
  match (counted.value, element) with
  | Some stop, Lent lending ->
      let start = Tree.Constant { value = Integer Z.zero; type_ = count.type_ } in
      let lent_part = ref None in
      for_loop ~lent:lent_part builder ~origin ~pattern:position
        ~iteration:(Range { start; stop; inclusive = false })
        ~loop
        ~each:(fun bind_position ->
          each (fun () ->
              bind_position ();
              Option.iter
                (fun (part : Tree.place) ->
                  (match part.root with
                  | Local element -> (
                      match lent_from builder element with
                      | Some collection ->
                          lent_part := Some { element; collection; count = counted }
                      | None -> bug "a loop over elements whose collection no call borrows")
                  | Constant _ | Literal _ -> bug "a loop over elements that a constant lends");
                  bind builder pattern part)
                (lent builder lending ~duration:Loop_body)))
  | Some _, _ -> bug "a loop over elements that no call lends"
  | None, _ -> ()

and lent_from builder part =
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
          Some (Emitter.borrowed_place builder place)
      | _ -> None)
    (Emitter.emitted builder)

and cursor_loop builder ~origin ~pattern ~cursor ~next ~loop ~each =
  match place builder cursor with
  | None -> ()
  | Some place_ ->
      let cursor_type = Core_walk.place_type cursor in
      let cursor = place_ in
      Option.iter
        (fun next ->
          for_loop ~cursor_type builder ~origin ~pattern
            ~iteration:(Pull { cursor; next })
            ~loop ~each)
        (callee_of builder next)

and quantifier_loop builder (node : Core.expression) (quantifier : Core.quantifier)
    (body : Core.expression) run =
  let origin = node.origin in
  let result = Emitter.temporary builder Types.bool origin in
  let quantified = ref None in
  let deciding = quantifier = Exists in
  Emitter.assign builder (Emitter.at result)
    (Operand (Constant { value = Boolean (not deciding); type_ = Types.bool }))
    origin;
  let loop_of () = { Tree.clauses = []; schedule = Sequential; origin; quantified = !quantified } in
  run ~loop:loop_of ~each:(fun bind_part ->
      Emitter.in_scope builder origin (fun () ->
          bind_part ();
          let binding_count = List.length (Emitter.emitted builder) in
          Option.iter
            (fun holds ->
              quantified :=
                Some
                  {
                    quantifier;
                    binding_count;
                    decision = List.length (Emitter.emitted builder);
                    holds;
                    decides = result;
                  };
              let decided =
                Emitter.block_of builder (fun () ->
                    Emitter.assign builder (Emitter.at result)
                      (Operand (Constant { value = Boolean deciding; type_ = Types.bool }))
                      origin;
                    Emitter.break_ builder origin;
                    None)
              and undecided = Emitter.block_of builder (fun () -> Some Emitter.unit_value) in
              ignore
                (Emitter.hold_choice builder Types.unit origin
                   (Conditional
                      {
                        condition = holds;
                        then_ = (if deciding then decided else undecided);
                        else_ = (if deciding then undecided else decided);
                        if_condition = None;
                      })))
            (expression builder body)));
  Some (Use { place = Emitter.at result; type_ = Types.bool; origin })

and quantified builder (node : Core.expression) (quantifier : Core.quantifier)
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
    | Over_collection { pattern; collection } ->
        ( Option.map
            (fun collection -> Tree.Over_collection collection)
            (expression builder collection),
          pattern.type_ )
    | Over_elements { pattern; elements } -> (
        match elements.count.kind with
        | Call { arguments = [ Passed { value = collection; _ } ]; _ } ->
            ( Option.map
                (fun collection -> Tree.Over_collection collection)
                (operand builder Read collection),
              pattern.type_ )
        | _ -> bug "a quantifier over elements whose count takes no collection")
  in
  let* range = range in
  let parameter, matches =
    match binder with
    | Over_type { local; name; type_ } ->
        ( Emitter.bind_source ~name builder local Own type_ origin,
          {
            Tree.statements = [];
            value = Some (Constant { value = Boolean true; type_ = Types.bool });
          } )
    | Over_range { pattern; _ } | Over_collection { pattern; _ } | Over_elements { pattern; _ } ->
        let parameter = Emitter.new_local builder Temporary value_type origin in
        ( parameter,
          Emitter.block_of builder (fun () ->
              match_patterns builder [ pattern ] [ Emitter.at parameter ] origin) )
  in
  let body = Emitter.block_of builder (fun () -> expression builder body) in
  Emitter.hold builder node.type_ origin
    (Specification (Quantified { quantifier; range; parameter; matches; body }))

and lambda builder (parameters : Core.pattern list) (captures : Core.capture list)
    (body : Core.block) =
  let inner = Emitter.for_lambda builder in
  let capture_locals =
    List.map
      (fun (capture : Core.capture) ->
        let name =
          match Option.map (Emitter.local_info builder) (Emitter.source builder capture.local) with
          | Some { kind = Source { name; _ }; _ } -> name
          | _ -> None
        in
        let local =
          Emitter.new_local inner
            (Source { local = capture.local; mode = Read; name; is_var = false })
            capture.type_ 0
        in
        Emitter.add_source inner capture.local local;
        local)
      captures
  in
  let parameter_locals =
    Emitter.in_scope inner 0 (fun () ->
        let locals =
          List.map
            (fun (pattern : Core.pattern) ->
              match pattern.kind with
              | Bind { local; mode; name; is_var } ->
                  Emitter.bind_source ~name ~is_var inner local mode pattern.type_ pattern.origin
              | _ -> Emitter.new_local inner Temporary pattern.type_ pattern.origin)
            parameters
        in
        List.iter2
          (fun (pattern : Core.pattern) local ->
            match pattern.kind with Bind _ -> () | _ -> bind inner pattern (Emitter.at local))
          parameters locals;
        Option.iter (fun value -> Emitter.return_ inner (Some value) 0) (block inner body);
        locals)
  in
  let rec unconverted (value : Core.expression) =
    match value.kind with
    | Convert { conversion = To_integer; value = inner } -> unconverted inner
    | _ -> value.type_
  in
  let body =
    Emitter.finish inner ~parameters:parameter_locals ~captures:capture_locals
      ~is_functional:(is_functional (fun visit -> Core_walk.block visit body))
      ?value_type:(Option.map unconverted body.value)
  in
  Emitter.add_lambda builder body

and block_type (body : Core.block) =
  match body.value with Some value -> value.type_ | None -> Types.unit

and of_proof ~entry_locals (written : Core.block) =
  let builder = Emitter.create ~is_specification:true ~entry_locals ~takes_free_locals:true () in
  Emitter.in_scope builder 0 (fun () ->
      Option.iter (fun value -> Emitter.return_ builder (Some value) 0) (block builder written));
  let body = Emitter.finish builder ~parameters:(Emitter.free_locals builder) in
  { body; lambdas = Emitter.lambdas builder }

and free_formula ~entry_locals ~origin ~type_ (build : Emitter.t -> Tree.operand option) =
  let builder = Emitter.create ~is_specification:true ~entry_locals ~takes_free_locals:true () in
  Emitter.formula builder ~origin ~type_ (fun () ->
      let value = build builder in
      (Emitter.free_locals builder, value))

and of_specification ~entry_locals (written : Core.expression) =
  free_formula ~entry_locals ~origin:written.origin ~type_:written.type_ (fun builder ->
      expression builder written)

and of_law_statement ~entry_locals (written : Core.block) =
  free_formula ~entry_locals ~origin:0 ~type_:(block_type written) (fun builder ->
      block builder written)

and attached builder (written : Core.expression) =
  of_specification ~entry_locals:(Emitter.entry_locals builder) written

and loop_clauses builder (clauses : Core.loop_clause list) : Tree.loop_clause list =
  let bound : Core.bound -> Tree.bound = function
    | Finite -> Finite
    | Order_of amount -> Order_of (attached builder amount)
    | At_most amount -> At_most (attached builder amount)
    | Exactly amount -> Exactly (attached builder amount)
  in
  List.map
    (function
      | Core.Invariant invariant -> Tree.Invariant (attached builder invariant)
      | Decreases measures -> Decreases (List.map (attached builder) measures)
      | Cost { origin; amortized; resource; bound = written } ->
          Cost { origin; amortized; resource; bound = bound written })
    clauses

let of_expression ?(parameters = []) (written : Core.expression) =
  let builder =
    Emitter.create
      ~entry_locals:(List.map (fun (parameter : Core.parameter) -> parameter.local) parameters)
      ()
  in
  let parameters =
    List.map
      (fun (parameter : Core.parameter) ->
        Emitter.bind_source ~name:parameter.name builder parameter.local parameter.mode
          parameter.type_ 0)
      parameters
  in
  Emitter.in_scope builder written.origin (fun () ->
      Emitter.in_statement builder written.origin (fun () ->
          Option.iter
            (fun value -> Emitter.return_ builder (Some value) written.origin)
            (expression builder written)));
  let body = Emitter.finish builder ~parameters in
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
        Emitter.bind_source ~name:parameter.name builder parameter.local parameter.mode
          parameter.type_ 0)
      parameters
  in
  Emitter.formula builder ~origin:written.origin ~type_:written.type_ (fun () ->
      (locals, expression builder written))

let of_definition ?(is_specification = false) (definition : Core.definition) =
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
            Emitter.bind_source ~name:parameter.name builder parameter.local parameter.mode
              parameter.type_ 0)
          parameters
      in
      Emitter.in_scope builder 0 (fun () ->
          Option.iter
            (fun value -> Emitter.return_ builder (if returns then Some value else None) 0)
            (block builder body));
      { Tree.body = Emitter.finish builder ~parameters:locals; lambdas = Emitter.lambdas builder })
    code

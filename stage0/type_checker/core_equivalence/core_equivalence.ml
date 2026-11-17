module Local_table = Hashtbl.Make (Structural_key.Make (struct
  type t = Core.local
end))

type parameters = Core.parameter list * Core.parameter list
type renaming = { forward : Core.local Local_table.t; backward : Core.local Local_table.t }

let corresponds renaming before after =
  match
    (Local_table.find_opt renaming.forward before, Local_table.find_opt renaming.backward after)
  with
  | Some paired, _ -> paired = after
  | None, Some _ -> false
  | None, None ->
      Local_table.replace renaming.forward before after;
      Local_table.replace renaming.backward after before;
      true

let copy renaming =
  { forward = Local_table.copy renaming.forward; backward = Local_table.copy renaming.backward }

let rename_parameters ((before, after) : parameters) =
  let renaming = { forward = Local_table.create 16; backward = Local_table.create 16 } in
  ignore (corresponds renaming Self Self);
  let rec pair = function
    | (was : Core.parameter) :: before, (now : Core.parameter) :: after ->
        ignore (corresponds renaming was.local now.local);
        pair (before, after)
    | _ -> ()
  in
  pair (before, after);
  renaming

let rec is_equivalent_place renaming (before : Core.place) (after : Core.place) =
  match (before, after) with
  | Local { local; type_; origin = _ }, Local after ->
      corresponds renaming local after.local && Types.equal type_ after.type_
  | Constant { path; type_; origin = _ }, Constant after ->
      Path.equal path after.path && Types.equal type_ after.type_
  | Field { base; field; type_; origin = _ }, Field after ->
      is_equivalent_place renaming base after.base
      && String.equal field after.field && Types.equal type_ after.type_
  | Lent before, Lent after | Temporary before, Temporary after ->
      is_equivalent_expression renaming before after
  | (Local _ | Constant _ | Field _ | Lent _ | Temporary _), _ -> false

and is_equivalent_operand renaming (before : Core.operand) (after : Core.operand) =
  match (before, after) with
  | Place before, Place after -> is_equivalent_place renaming before after
  | Value before, Value after -> is_equivalent_expression renaming before after
  | (Place _ | Value _), _ -> false

and is_equivalent_callee renaming (before : Core.callee) (after : Core.callee) =
  match (before, after) with
  | Function { path; type_arguments }, Function after ->
      Path.equal path after.path && type_arguments = after.type_arguments
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence }, Trait_method after
    ->
      trait = after.trait && String.equal name after.name && receiver = after.receiver
      && Types.equal self_type after.self_type
      && type_arguments = after.type_arguments
      && evidence = after.evidence
  | Capability_method { capability; name }, Capability_method after ->
      Path.equal capability after.capability && String.equal name after.name
  | Intrinsic { operation; type_arguments }, Intrinsic after ->
      operation = after.operation && type_arguments = after.type_arguments
  | Indirect before, Indirect after -> is_equivalent_operand renaming before after
  | (Function _ | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _), _ -> false

and is_equivalent_call renaming ({ callee = called; arguments; lends; uses } : Core.call)
    (after : Core.call) =
  is_equivalent_callee renaming called after.callee
  && List.equal (is_equivalent_argument renaming) arguments after.arguments
  && lends = after.lends && uses = after.uses

and is_equivalent_argument renaming (before : Core.argument) (after : Core.argument) =
  match (before, after) with
  | Passed { mode; value }, Passed after ->
      mode = after.mode && is_equivalent_operand renaming value after.value
  | Default, Default -> true
  | (Passed _ | Default), _ -> false

and is_equivalent_expression renaming ({ id = _; origin = _; type_; kind = form } : Core.expression)
    (after : Core.expression) =
  Types.equal type_ after.type_ && is_equivalent_kind renaming form after.kind

and is_equivalent_kind renaming (before : Core.kind) (after : Core.kind) =
  match (before, after) with
  | Integer before, Integer after -> Z.equal before after
  | Float before, Float after -> Float.equal before after
  | Boolean before, Boolean after -> Bool.equal before after
  | String before, String after -> String.equal before after
  | Checked_literal { subject; call }, Checked_literal after ->
      subject = after.subject && is_equivalent_expression renaming call after.call
  | Use before, Use after -> is_equivalent_place renaming before after
  | Copy before, Copy after -> is_equivalent_operand renaming before after
  | Function_value { path; type_arguments }, Function_value after ->
      Path.equal path after.path && type_arguments = after.type_arguments
  | Value_parameter before, Value_parameter after -> before = after
  | Lambda { parameters; captures; body; result }, Lambda after ->
      List.equal (is_equivalent_pattern renaming) parameters after.parameters
      && List.equal (is_equivalent_capture renaming) captures after.captures
      && is_equivalent_block renaming body after.body
      && Types.equal result after.result
  | Construct { variant; fields }, Construct after ->
      Option.equal String.equal variant after.variant
      && List.equal
           (fun (name, value) (after_name, after_value) ->
             String.equal name after_name
             && Option.equal (is_equivalent_operand renaming) value after_value)
           fields after.fields
  | Collection_literal { elements; construction }, Collection_literal after ->
      List.equal (is_equivalent_expression renaming) elements after.elements
      && construction = after.construction
  | Map_literal { entries }, Map_literal after ->
      List.equal
        (fun (key, value) (after_key, after_value) ->
          is_equivalent_expression renaming key after_key
          && is_equivalent_expression renaming value after_value)
        entries after.entries
  | Record_update { base; updates }, Record_update after ->
      is_equivalent_expression renaming base after.base
      && List.equal
           (fun (fields, value) (after_fields, after_value) ->
             List.equal String.equal fields after_fields
             && is_equivalent_expression renaming value after_value)
           updates after.updates
  | Slice { base; callee = sliced; bounds }, Slice after ->
      is_equivalent_operand renaming (Place base) (Place after.base)
      && is_equivalent_callee renaming sliced after.callee
      && List.equal (is_equivalent_argument renaming) bounds after.bounds
  | Call before, Call after -> is_equivalent_call renaming before after
  | Operator { operation; arguments }, Operator after ->
      operation = after.operation
      && List.equal (is_equivalent_expression renaming) arguments after.arguments
  | Compare { comparison; left; right }, Compare after ->
      comparison = after.comparison
      && is_equivalent_expression renaming left after.left
      && is_equivalent_expression renaming right after.right
  | Not before, Not after | Echo before, Echo after | Old before, Old after ->
      is_equivalent_expression renaming before after
  | And (first, second), And (after_first, after_second)
  | Or (first, second), Or (after_first, after_second)
  | Implies (first, second), Implies (after_first, after_second)
  | Identical (first, second), Identical (after_first, after_second) ->
      is_equivalent_expression renaming first after_first
      && is_equivalent_expression renaming second after_second
  | Matches { value; pattern = tested }, Matches after ->
      is_equivalent_operand renaming value after.value
      && is_equivalent_pattern renaming tested after.pattern
  | Convert { conversion; value }, Convert after ->
      conversion = after.conversion && is_equivalent_expression renaming value after.value
  | To_any { value; trait; evidence }, To_any after ->
      is_equivalent_expression renaming value after.value
      && trait = after.trait && evidence = after.evidence
  | If { condition = tested; then_; else_; binds_lent_part }, If after ->
      is_equivalent_expression renaming tested after.condition
      && is_equivalent_block renaming then_ after.then_
      && Option.equal (is_equivalent_block renaming) else_ after.else_
      && Bool.equal binds_lent_part after.binds_lent_part
  | Match { scrutinees; arms }, Match after ->
      List.equal (is_equivalent_operand renaming) scrutinees after.scrutinees
      && List.equal (is_equivalent_arm renaming) arms after.arms
  | Block before, Block after -> is_equivalent_block renaming before after
  | Provide { implementations; body }, Provide after ->
      List.equal (is_equivalent_implementation renaming) implementations after.implementations
      && is_equivalent_block renaming body after.body
  | Return before, Return after -> Option.equal (is_equivalent_expression renaming) before after
  | Break, Break
  | Continue, Continue
  | Todo, Todo
  | Unreachable, Unreachable
  | Result, Result
  | Current_target, Current_target
  | Yielded, Yielded ->
      true
  | Quantified { quantifier; binder = bound; body }, Quantified after ->
      quantifier = after.quantifier
      && is_equivalent_binder renaming bound after.binder
      && is_equivalent_expression renaming body after.body
  | Specification_function { function_; arguments }, Specification_function after ->
      function_ = after.function_
      && List.equal (is_equivalent_expression renaming) arguments after.arguments
  | Method_time before, Method_time after -> is_equivalent_callee renaming before after
  | ( ( Integer _ | Float _ | Boolean _ | String _ | Checked_literal _ | Use _ | Copy _
      | Function_value _ | Value_parameter _ | Lambda _ | Construct _ | Collection_literal _
      | Map_literal _ | Record_update _ | Slice _ | Call _ | Operator _ | Compare _ | Not _ | And _
      | Or _ | Implies _ | Matches _ | Convert _ | To_any _ | If _ | Match _ | Block _ | Provide _
      | Return _ | Break | Continue | Todo | Unreachable | Echo _ | Result | Old _ | Current_target
      | Quantified _ | Yielded | Identical _ | Specification_function _ | Method_time _ ),
      _ ) ->
      false

and is_equivalent_capture renaming ({ local; type_ } : Core.capture) (after : Core.capture) =
  corresponds renaming local after.local && Types.equal type_ after.type_

and is_equivalent_binder renaming (before : Core.binder) (after : Core.binder) =
  match (before, after) with
  | Over_type { local; type_ }, Over_type after ->
      corresponds renaming local after.local && Types.equal type_ after.type_
  | Over_range { pattern = bound; start; stop; inclusive }, Over_range after ->
      is_equivalent_pattern renaming bound after.pattern
      && is_equivalent_expression renaming start after.start
      && is_equivalent_expression renaming stop after.stop
      && Bool.equal inclusive after.inclusive
  | Over_elements { pattern = bound; elements = counted }, Over_elements after ->
      is_equivalent_pattern renaming bound after.pattern
      && is_equivalent_elements renaming counted after.elements
  | (Over_type _ | Over_range _ | Over_elements _), _ -> false

and is_equivalent_elements renaming ({ count; position; element } : Core.elements)
    (after : Core.elements) =
  is_equivalent_expression renaming count after.count
  && is_equivalent_pattern renaming position after.position
  && is_equivalent_place renaming element after.element

and is_equivalent_implementation renaming
    ({ origin = _; mode; value; type_; provides } : Core.implementation)
    (after : Core.implementation) =
  mode = after.mode
  && is_equivalent_operand renaming value after.value
  && Types.equal type_ after.type_ && provides = after.provides

and is_equivalent_block renaming ({ statements; value } : Core.block) (after : Core.block) =
  List.equal (is_equivalent_statement renaming) statements after.statements
  && Option.equal (is_equivalent_expression renaming) value after.value

and is_equivalent_statement renaming ({ id = _; origin = _; kind = form } : Core.statement)
    (after : Core.statement) =
  match (form, after.kind) with
  | Let { pattern = bound; value; else_ }, Let after ->
      is_equivalent_operand renaming value after.value
      && is_equivalent_pattern renaming bound after.pattern
      && Option.equal (is_equivalent_block renaming) else_ after.else_
  | Evaluate before, Evaluate after -> is_equivalent_expression renaming before after
  | Assign { target; value }, Assign after ->
      is_equivalent_place renaming target after.target
      && is_equivalent_expression renaming value after.value
  | Compound_assign { target; operand = read; bound; value }, Compound_assign after ->
      is_equivalent_place renaming target after.target
      && is_equivalent_operand renaming read after.operand
      && corresponds renaming bound after.bound
      && is_equivalent_expression renaming value after.value
  | For { pattern = bound; iteration = iterated; clauses; body; mode }, For after ->
      is_equivalent_iteration renaming iterated after.iteration
      && is_equivalent_pattern renaming bound after.pattern
      && List.equal (is_equivalent_loop_clause renaming) clauses after.clauses
      && is_equivalent_block renaming body after.body
      && mode = after.mode
  | While { condition = tested; clauses; body; binds_lent_part }, While after ->
      is_equivalent_expression renaming tested after.condition
      && List.equal (is_equivalent_loop_clause renaming) clauses after.clauses
      && is_equivalent_block renaming body after.body
      && Bool.equal binds_lent_part after.binds_lent_part
  | Parallel before, Parallel after | Concurrent before, Concurrent after ->
      List.equal (is_equivalent_statement renaming) before after
  | Proof before, Proof after -> is_equivalent_block renaming before after
  | Assert { condition = asserted; by_bit_vector }, Assert after ->
      is_equivalent_condition renaming asserted after.condition
      && Bool.equal by_bit_vector after.by_bit_vector
  | Yield { mode; part }, Yield after ->
      mode = after.mode && is_equivalent_operand renaming part after.part
  | ( ( Let _ | Evaluate _ | Assign _ | Compound_assign _ | For _ | While _ | Parallel _
      | Concurrent _ | Proof _ | Assert _ | Yield _ ),
      _ ) ->
      false

and is_equivalent_iteration renaming (before : Core.iteration) (after : Core.iteration) =
  match (before, after) with
  | Integer_range { start; stop; inclusive }, Integer_range after ->
      is_equivalent_expression renaming start after.start
      && is_equivalent_expression renaming stop after.stop
      && Bool.equal inclusive after.inclusive
  | Elements before, Elements after -> is_equivalent_elements renaming before after
  | Cursor { cursor; next }, Cursor after ->
      is_equivalent_place renaming cursor after.cursor
      && is_equivalent_callee renaming next after.next
  | (Integer_range _ | Elements _ | Cursor _), _ -> false

and is_equivalent_loop_clause renaming (before : Core.loop_clause) (after : Core.loop_clause) =
  match (before, after) with
  | Invariant before, Invariant after -> is_equivalent_expression renaming before after
  | Decreases before, Decreases after -> List.equal (is_equivalent_expression renaming) before after
  | Cost before, Cost after -> is_equivalent_cost renaming before after
  | (Invariant _ | Decreases _ | Cost _), _ -> false

and is_equivalent_cost renaming
    ({ origin = _; amortized; resource = spent; bound = limit } : Core.cost) (after : Core.cost) =
  Bool.equal amortized after.amortized
  && is_equivalent_resource renaming spent after.resource
  && is_equivalent_bound renaming limit after.bound

and is_equivalent_resource renaming (before : Core.resource) (after : Core.resource) =
  match (before, after) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls before, Calls after -> is_equivalent_calls_target renaming before after
  | (Time | Allocations | Allocated_bytes | Calls _), _ -> false

and is_equivalent_calls_target renaming (before : Core.calls_target) (after : Core.calls_target) =
  match (before, after) with
  | Function_parameter before, Function_parameter after -> corresponds renaming before after
  | Capability before, Capability after -> Path.equal before after
  | Capability_method (capability, name), Capability_method (after_capability, after_name) ->
      Path.equal capability after_capability && String.equal name after_name
  | (Function_parameter _ | Capability _ | Capability_method _), _ -> false

and is_equivalent_bound renaming (before : Core.bound) (after : Core.bound) =
  match (before, after) with
  | Finite, Finite -> true
  | Order_of before, Order_of after | At_most before, At_most after | Exactly before, Exactly after
    ->
      is_equivalent_expression renaming before after
  | (Finite | Order_of _ | At_most _ | Exactly _), _ -> false

and is_equivalent_condition renaming ({ value; executable } : Core.condition)
    (after : Core.condition) =
  is_equivalent_expression renaming value after.value && Bool.equal executable after.executable

and is_equivalent_arm renaming ({ patterns; guard; body; origin = _ } : Core.arm) (after : Core.arm)
    =
  List.equal (is_equivalent_pattern renaming) patterns after.patterns
  && Option.equal (is_equivalent_expression renaming) guard after.guard
  && is_equivalent_block renaming body after.body

and is_equivalent_pattern renaming ({ id = _; origin = _; type_; kind = form } : Core.pattern)
    (after : Core.pattern) =
  Types.equal type_ after.type_
  &&
  match (form, after.kind) with
  | Wildcard, Wildcard -> true
  | Bind { local; is_var; mode }, Bind after ->
      corresponds renaming local after.local && Bool.equal is_var after.is_var && mode = after.mode
  | Variant { variant; fields }, Variant after ->
      String.equal variant after.variant
      && List.equal (is_equivalent_field_pattern renaming) fields after.fields
  | Record before, Record after -> List.equal (is_equivalent_field_pattern renaming) before after
  | Literal before, Literal after -> is_equivalent_pattern_constant before after
  | Range { start; stop; inclusive }, Range after ->
      is_equivalent_range_bound start after.start
      && is_equivalent_range_bound stop after.stop
      && Bool.equal inclusive after.inclusive
  | Equal_to { value; equal }, Equal_to after ->
      is_equivalent_pattern_constant value after.value
      && is_equivalent_callee renaming equal after.equal
  | Alternatives before, Alternatives after ->
      List.equal (is_equivalent_pattern renaming) before after
  | ( (Wildcard | Bind _ | Variant _ | Record _ | Literal _ | Range _ | Equal_to _ | Alternatives _),
      _ ) ->
      false

and is_equivalent_field_pattern renaming (name, bound) (after_name, after_bound) =
  String.equal name after_name && is_equivalent_pattern renaming bound after_bound

and is_equivalent_pattern_constant (before : Core.pattern_constant) (after : Core.pattern_constant)
    =
  match (before, after) with
  | Boolean_constant before, Boolean_constant after -> Bool.equal before after
  | Integer_constant before, Integer_constant after -> Z.equal before after
  | String_constant before, String_constant after -> String.equal before after
  | Named_constant before, Named_constant after -> Path.equal before after
  | (Boolean_constant _ | Integer_constant _ | String_constant _ | Named_constant _), _ -> false

and is_equivalent_range_bound (before : Core.range_bound) (after : Core.range_bound) =
  match (before, after) with
  | Integer_bound before, Integer_bound after -> Z.equal before after
  | Constant_bound before, Constant_bound after -> Path.equal before after
  | (Integer_bound _ | Constant_bound _), _ -> false

let is_equivalent_callback_contract renaming ({ inputs; requires } : Core.callback_contract)
    (after : Core.callback_contract) =
  List.equal (corresponds renaming) inputs after.inputs
  && List.equal (is_equivalent_expression renaming) requires after.requires

let is_equivalent_parameter renaming
    ({ local; mode; type_; default; callback_contract = contract } : Core.parameter)
    (after : Core.parameter) =
  corresponds renaming local after.local
  && Option.equal String.equal (Core_walk.find_local_name local)
       (Core_walk.find_local_name after.local)
  && mode = after.mode && Types.equal type_ after.type_
  && Option.equal (is_equivalent_expression renaming) default after.default
  && Option.equal (is_equivalent_callback_contract renaming) contract after.callback_contract

let equal_condition ~parameters before after =
  is_equivalent_condition (rename_parameters parameters) before after

let equal_expression ~parameters before after =
  is_equivalent_expression (rename_parameters parameters) before after

let equal_cost ~parameters before after =
  is_equivalent_cost (rename_parameters parameters) before after

let equal_law ({ name; parameters; requires; body } : Core.law) (after : Core.law) =
  let renaming = rename_parameters ([], []) in
  let is_still_required was =
    List.exists (fun now -> is_equivalent_expression (copy renaming) was now) after.requires
  in
  let was_required now =
    List.exists (fun was -> is_equivalent_expression (copy renaming) was now) requires
  in
  String.equal name after.name
  && List.equal (is_equivalent_parameter renaming) parameters after.parameters
  && List.for_all is_still_required requires
  && List.for_all was_required after.requires
  && is_equivalent_block renaming body after.body

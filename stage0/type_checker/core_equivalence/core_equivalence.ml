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

let rec place renaming (before : Core.place) (after : Core.place) =
  match (before, after) with
  | Local { local; type_; origin = _ }, Local after ->
      corresponds renaming local after.local && Types.equal type_ after.type_
  | Constant { path; type_; origin = _ }, Constant after ->
      Path.equal path after.path && Types.equal type_ after.type_
  | Field { base; field; type_; origin = _ }, Field after ->
      place renaming base after.base && String.equal field after.field
      && Types.equal type_ after.type_
  | Lent before, Lent after | Temporary before, Temporary after -> expression renaming before after
  | (Local _ | Constant _ | Field _ | Lent _ | Temporary _), _ -> false

and operand renaming (before : Core.operand) (after : Core.operand) =
  match (before, after) with
  | Place before, Place after -> place renaming before after
  | Value before, Value after -> expression renaming before after
  | (Place _ | Value _), _ -> false

and callee renaming (before : Core.callee) (after : Core.callee) =
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
  | Indirect before, Indirect after -> operand renaming before after
  | (Function _ | Trait_method _ | Capability_method _ | Intrinsic _ | Indirect _), _ -> false

and call renaming ({ callee = called; arguments; lends; uses } : Core.call) (after : Core.call) =
  callee renaming called after.callee
  && List.equal (argument renaming) arguments after.arguments
  && lends = after.lends && uses = after.uses

and argument renaming (before : Core.argument) (after : Core.argument) =
  match (before, after) with
  | Passed { mode; value; mode_keyword = _ }, Passed after ->
      mode = after.mode && operand renaming value after.value
  | Default, Default -> true
  | (Passed _ | Default), _ -> false

and expression renaming ({ id = _; origin = _; type_; kind = form } : Core.expression)
    (after : Core.expression) =
  Types.equal type_ after.type_ && kind renaming form after.kind

and kind renaming (before : Core.kind) (after : Core.kind) =
  match (before, after) with
  | Integer before, Integer after -> Z.equal before after
  | Float before, Float after -> Float.equal before after
  | Boolean before, Boolean after -> Bool.equal before after
  | String before, String after -> String.equal before after
  | Template { literals; call }, Template after ->
      List.equal String.equal literals after.literals && expression renaming call after.call
  | Use before, Use after -> place renaming before after
  | Copy before, Copy after -> operand renaming before after
  | Function_value { path; type_arguments }, Function_value after ->
      Path.equal path after.path && type_arguments = after.type_arguments
  | Value_parameter before, Value_parameter after -> before = after
  | Lambda { parameters; captures; body; result }, Lambda after ->
      List.equal (pattern renaming) parameters after.parameters
      && List.equal (capture renaming) captures after.captures
      && block renaming body after.body && Types.equal result after.result
  | Construct { variant; fields }, Construct after ->
      Option.equal String.equal variant after.variant
      && List.equal
           (fun (name, value) (after_name, after_value) ->
             String.equal name after_name && Option.equal (operand renaming) value after_value)
           fields after.fields
  | Collection_literal { elements; construction }, Collection_literal after ->
      List.equal (expression renaming) elements after.elements && construction = after.construction
  | Map_literal { entries }, Map_literal after ->
      List.equal
        (fun (key, value) (after_key, after_value) ->
          expression renaming key after_key && expression renaming value after_value)
        entries after.entries
  | Record_update { base; updates }, Record_update after ->
      expression renaming base after.base
      && List.equal
           (fun (fields, value) (after_fields, after_value) ->
             List.equal String.equal fields after_fields && expression renaming value after_value)
           updates after.updates
  | Slice { base; callee = sliced; bounds }, Slice after ->
      operand renaming (Place base) (Place after.base)
      && callee renaming sliced after.callee
      && List.equal (argument renaming) bounds after.bounds
  | Call before, Call after -> call renaming before after
  | Operator { operation; arguments }, Operator after ->
      operation = after.operation && List.equal (expression renaming) arguments after.arguments
  | Compare { comparison; left; right }, Compare after ->
      comparison = after.comparison
      && expression renaming left after.left
      && expression renaming right after.right
  | Not before, Not after | Echo before, Echo after | Old before, Old after ->
      expression renaming before after
  | And (first, second), And (after_first, after_second)
  | Or (first, second), Or (after_first, after_second)
  | Implies (first, second), Implies (after_first, after_second)
  | Identical (first, second), Identical (after_first, after_second) ->
      expression renaming first after_first && expression renaming second after_second
  | Matches { value; pattern = tested }, Matches after ->
      operand renaming value after.value && pattern renaming tested after.pattern
  | Convert { conversion; value }, Convert after ->
      conversion = after.conversion && expression renaming value after.value
  | To_any { value; trait; evidence }, To_any after ->
      expression renaming value after.value && trait = after.trait && evidence = after.evidence
  | If { condition = tested; then_; else_; binds_lent_part }, If after ->
      expression renaming tested after.condition
      && block renaming then_ after.then_
      && Option.equal (block renaming) else_ after.else_
      && Bool.equal binds_lent_part after.binds_lent_part
  | Match { scrutinees; arms }, Match after ->
      List.equal (operand renaming) scrutinees after.scrutinees
      && List.equal (arm renaming) arms after.arms
  | Block before, Block after -> block renaming before after
  | Provide { implementations; body }, Provide after ->
      List.equal (implementation renaming) implementations after.implementations
      && block renaming body after.body
  | Return before, Return after -> Option.equal (expression renaming) before after
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
      && binder renaming bound after.binder
      && expression renaming body after.body
  | Specification_function { function_; arguments }, Specification_function after ->
      function_ = after.function_ && List.equal (expression renaming) arguments after.arguments
  | Method_time before, Method_time after -> callee renaming before after
  | ( ( Integer _ | Float _ | Boolean _ | String _ | Template _ | Use _ | Copy _ | Function_value _
      | Value_parameter _ | Lambda _ | Construct _ | Collection_literal _ | Map_literal _
      | Record_update _ | Slice _ | Call _ | Operator _ | Compare _ | Not _ | And _ | Or _
      | Implies _ | Matches _ | Convert _ | To_any _ | If _ | Match _ | Block _ | Provide _
      | Return _ | Break | Continue | Todo | Unreachable | Echo _ | Result | Old _ | Current_target
      | Quantified _ | Yielded | Identical _ | Specification_function _ | Method_time _ ),
      _ ) ->
      false

and capture renaming ({ local; type_ } : Core.capture) (after : Core.capture) =
  corresponds renaming local after.local && Types.equal type_ after.type_

and binder renaming (before : Core.binder) (after : Core.binder) =
  match (before, after) with
  | Over_type { local; name = _; type_ }, Over_type after ->
      corresponds renaming local after.local && Types.equal type_ after.type_
  | Over_range { pattern = bound; start; stop; inclusive }, Over_range after ->
      pattern renaming bound after.pattern
      && expression renaming start after.start
      && expression renaming stop after.stop
      && Bool.equal inclusive after.inclusive
  | Over_collection { pattern = bound; collection }, Over_collection after ->
      pattern renaming bound after.pattern && expression renaming collection after.collection
  | Over_elements { pattern = bound; elements = counted }, Over_elements after ->
      pattern renaming bound after.pattern && elements renaming counted after.elements
  | (Over_type _ | Over_range _ | Over_collection _ | Over_elements _), _ -> false

and elements renaming ({ count; position; element } : Core.elements) (after : Core.elements) =
  expression renaming count after.count
  && pattern renaming position after.position
  && place renaming element after.element

and implementation renaming ({ origin = _; mode; value; type_; provides } : Core.implementation)
    (after : Core.implementation) =
  mode = after.mode
  && operand renaming value after.value
  && Types.equal type_ after.type_ && provides = after.provides

and block renaming ({ statements; value } : Core.block) (after : Core.block) =
  List.equal (statement renaming) statements after.statements
  && Option.equal (expression renaming) value after.value

and statement renaming ({ id = _; origin = _; kind = form } : Core.statement)
    (after : Core.statement) =
  match (form, after.kind) with
  | Let { pattern = bound; value; else_ }, Let after ->
      operand renaming value after.value
      && pattern renaming bound after.pattern
      && Option.equal (block renaming) else_ after.else_
  | Evaluate before, Evaluate after -> expression renaming before after
  | Assign { target; value }, Assign after ->
      place renaming target after.target && expression renaming value after.value
  | Compound_assign { target; operand = read; bound; value }, Compound_assign after ->
      place renaming target after.target
      && operand renaming read after.operand
      && corresponds renaming bound after.bound
      && expression renaming value after.value
  | For { pattern = bound; iteration = iterated; clauses; body; mode }, For after ->
      iteration renaming iterated after.iteration
      && pattern renaming bound after.pattern
      && List.equal (loop_clause renaming) clauses after.clauses
      && block renaming body after.body && mode = after.mode
  | While { condition = tested; clauses; body; binds_lent_part }, While after ->
      expression renaming tested after.condition
      && List.equal (loop_clause renaming) clauses after.clauses
      && block renaming body after.body
      && Bool.equal binds_lent_part after.binds_lent_part
  | Parallel before, Parallel after | Concurrent before, Concurrent after ->
      List.equal (statement renaming) before after
  | Proof before, Proof after -> block renaming before after
  | Assert { condition = asserted; by_bit_vector }, Assert after ->
      condition renaming asserted after.condition && Bool.equal by_bit_vector after.by_bit_vector
  | Yield { mode; part }, Yield after -> mode = after.mode && operand renaming part after.part
  | ( ( Let _ | Evaluate _ | Assign _ | Compound_assign _ | For _ | While _ | Parallel _
      | Concurrent _ | Proof _ | Assert _ | Yield _ ),
      _ ) ->
      false

and iteration renaming (before : Core.iteration) (after : Core.iteration) =
  match (before, after) with
  | Integer_range { start; stop; inclusive }, Integer_range after ->
      expression renaming start after.start
      && expression renaming stop after.stop
      && Bool.equal inclusive after.inclusive
  | Elements before, Elements after -> elements renaming before after
  | Cursor { cursor; next }, Cursor after ->
      place renaming cursor after.cursor && callee renaming next after.next
  | (Integer_range _ | Elements _ | Cursor _), _ -> false

and loop_clause renaming (before : Core.loop_clause) (after : Core.loop_clause) =
  match (before, after) with
  | Invariant before, Invariant after -> expression renaming before after
  | Decreases before, Decreases after -> List.equal (expression renaming) before after
  | Cost before, Cost after -> cost renaming before after
  | (Invariant _ | Decreases _ | Cost _), _ -> false

and cost renaming ({ origin = _; amortized; resource = spent; bound = limit } : Core.cost)
    (after : Core.cost) =
  Bool.equal amortized after.amortized
  && resource renaming spent after.resource
  && bound renaming limit after.bound

and resource renaming (before : Core.resource) (after : Core.resource) =
  match (before, after) with
  | Time, Time | Allocations, Allocations | Allocated_bytes, Allocated_bytes -> true
  | Calls before, Calls after -> calls_target renaming before after
  | (Time | Allocations | Allocated_bytes | Calls _), _ -> false

and calls_target renaming (before : Core.calls_target) (after : Core.calls_target) =
  match (before, after) with
  | Function_parameter before, Function_parameter after -> corresponds renaming before after
  | Capability before, Capability after -> Path.equal before after
  | Capability_method (capability, name), Capability_method (after_capability, after_name) ->
      Path.equal capability after_capability && String.equal name after_name
  | (Function_parameter _ | Capability _ | Capability_method _), _ -> false

and bound renaming (before : Core.bound) (after : Core.bound) =
  match (before, after) with
  | Finite, Finite -> true
  | Order_of before, Order_of after | At_most before, At_most after | Exactly before, Exactly after
    ->
      expression renaming before after
  | (Finite | Order_of _ | At_most _ | Exactly _), _ -> false

and condition renaming ({ value; executable } : Core.condition) (after : Core.condition) =
  expression renaming value after.value && Bool.equal executable after.executable

and arm renaming ({ patterns; guard; body; origin = _ } : Core.arm) (after : Core.arm) =
  List.equal (pattern renaming) patterns after.patterns
  && Option.equal (expression renaming) guard after.guard
  && block renaming body after.body

and pattern renaming ({ id = _; origin = _; type_; kind = form } : Core.pattern)
    (after : Core.pattern) =
  Types.equal type_ after.type_
  &&
  match (form, after.kind) with
  | Wildcard, Wildcard -> true
  | Bind { local; name = _; is_var; mode }, Bind after ->
      corresponds renaming local after.local && Bool.equal is_var after.is_var && mode = after.mode
  | Variant { variant; fields }, Variant after ->
      String.equal variant after.variant && List.equal (field_pattern renaming) fields after.fields
  | Record before, Record after -> List.equal (field_pattern renaming) before after
  | Literal before, Literal after -> pattern_constant before after
  | Range { start; stop; inclusive }, Range after ->
      range_bound start after.start && range_bound stop after.stop
      && Bool.equal inclusive after.inclusive
  | Equal_to { value; equal }, Equal_to after ->
      pattern_constant value after.value && callee renaming equal after.equal
  | Alternatives before, Alternatives after -> List.equal (pattern renaming) before after
  | ( (Wildcard | Bind _ | Variant _ | Record _ | Literal _ | Range _ | Equal_to _ | Alternatives _),
      _ ) ->
      false

and field_pattern renaming (name, bound) (after_name, after_bound) =
  String.equal name after_name && pattern renaming bound after_bound

and pattern_constant (before : Core.pattern_constant) (after : Core.pattern_constant) =
  match (before, after) with
  | Boolean_constant before, Boolean_constant after -> Bool.equal before after
  | Integer_constant before, Integer_constant after -> Z.equal before after
  | String_constant before, String_constant after -> String.equal before after
  | Named_constant before, Named_constant after -> Path.equal before after
  | (Boolean_constant _ | Integer_constant _ | String_constant _ | Named_constant _), _ -> false

and range_bound (before : Core.range_bound) (after : Core.range_bound) =
  match (before, after) with
  | Integer_bound before, Integer_bound after -> Z.equal before after
  | Constant_bound before, Constant_bound after -> Path.equal before after
  | (Integer_bound _ | Constant_bound _), _ -> false

let callback_contract renaming ({ inputs; requires } : Core.callback_contract)
    (after : Core.callback_contract) =
  List.equal
    (fun (local, _) (after_local, _) -> corresponds renaming local after_local)
    inputs after.inputs
  && List.equal (expression renaming) requires after.requires

let parameter renaming
    ({ local; name; mode; type_; default; callback_contract = contract } : Core.parameter)
    (after : Core.parameter) =
  corresponds renaming local after.local
  && String.equal name after.name && mode = after.mode && Types.equal type_ after.type_
  && Option.equal (expression renaming) default after.default
  && Option.equal (callback_contract renaming) contract after.callback_contract

let equal_condition ~parameters before after = condition (rename_parameters parameters) before after

let equal_expression ~parameters before after =
  expression (rename_parameters parameters) before after

let equal_cost ~parameters before after = cost (rename_parameters parameters) before after

let equal_law ({ name; parameters; requires; body } : Core.law) (after : Core.law) =
  let renaming = rename_parameters ([], []) in
  let is_still_required was =
    List.exists (fun now -> expression (copy renaming) was now) after.requires
  in
  let was_required now = List.exists (fun was -> expression (copy renaming) was now) requires in
  String.equal name after.name
  && List.equal (parameter renaming) parameters after.parameters
  && List.for_all is_still_required requires
  && List.for_all was_required after.requires
  && block renaming body after.body

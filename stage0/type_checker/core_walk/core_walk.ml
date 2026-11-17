type visit = {
  expression : Core.expression -> unit;
  statement : Core.statement -> unit;
  pattern : Core.pattern -> unit;
  callee : Core.callee -> unit;
  place : Core.place -> unit;
}

let ignore_all =
  { expression = ignore; statement = ignore; pattern = ignore; callee = ignore; place = ignore }

let make_callee_visitor on_callee =
  {
    ignore_all with
    expression =
      (fun node -> match node.kind with Call { callee; _ } -> on_callee callee | _ -> ());
    callee = on_callee;
  }

let compute_place_type : Core.place -> Types.ty = function
  | Local { type_; _ } | Constant { type_; _ } | Field { type_; _ } -> type_
  | Lent value | Temporary value -> value.type_

let compute_place_origin : Core.place -> Core.origin = function
  | Local { origin; _ } | Constant { origin; _ } | Field { origin; _ } -> origin
  | Lent value | Temporary value -> value.origin

let rec walk_place visit core_place =
  visit.place core_place;
  match core_place with
  | Local _ | Constant _ -> ()
  | Field { base; _ } -> walk_place visit base
  | Lent call -> visit.expression call
  | Temporary value -> visit.expression value

let walk_operand visit = function
  | Core.Place core_place -> walk_place visit core_place
  | Value value -> visit.expression value

let walk_block visit (body : Core.block) =
  List.iter visit.statement body.statements;
  Option.iter visit.expression body.value

let walk_cost visit (cost : Core.cost) =
  match cost.bound with
  | Finite -> ()
  | Order_of value | At_most value | Exactly value -> visit.expression value

let walk_loop_clause visit = function
  | Core.Invariant value -> visit.expression value
  | Decreases measures -> List.iter visit.expression measures
  | Cost bound -> walk_cost visit bound

let walk_expression_children visit (node : Core.expression) =
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _ | Break
  | Continue | Todo | Unreachable | Result | Current_target | Yielded | Method_time _ ->
      ()
  | Template { call; _ } -> visit.expression call
  | Use core_place -> walk_place visit core_place
  | Copy value -> walk_operand visit value
  | Lambda { parameters; body; _ } ->
      List.iter visit.pattern parameters;
      walk_block visit body
  | Construct { fields; _ } ->
      List.iter (fun (_, value) -> Option.iter (walk_operand visit) value) fields
  | Collection_literal { elements; _ } -> List.iter visit.expression elements
  | Map_literal { entries } ->
      List.iter
        (fun (key, value) ->
          visit.expression key;
          visit.expression value)
        entries
  | Record_update { base; updates } ->
      visit.expression base;
      List.iter (fun (_, value) -> visit.expression value) updates
  | Slice { base; callee; bounds } ->
      walk_place visit base;
      visit.callee callee;
      List.iter
        (function Core.Passed { value; _ } -> walk_operand visit value | Default -> ())
        bounds
  | Call call ->
      (match call.callee with
      | Indirect function_value -> walk_operand visit function_value
      | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ());
      List.iter
        (function Core.Passed { value; _ } -> walk_operand visit value | Default -> ())
        call.arguments
  | Operator { arguments; _ } | Specification_function { arguments; _ } ->
      List.iter visit.expression arguments
  | Compare { left; right; _ }
  | And (left, right)
  | Or (left, right)
  | Implies (left, right)
  | Identical (left, right) ->
      visit.expression left;
      visit.expression right
  | Not inner | Echo inner | Old inner | To_any { value = inner; _ } -> visit.expression inner
  | Matches { value; pattern } ->
      walk_operand visit value;
      visit.pattern pattern
  | Convert { value; _ } -> visit.expression value
  | If { condition; then_; else_; _ } ->
      visit.expression condition;
      walk_block visit then_;
      Option.iter (walk_block visit) else_
  | Match { scrutinees; arms; _ } ->
      List.iter (walk_operand visit) scrutinees;
      List.iter
        (fun (arm : Core.arm) ->
          List.iter visit.pattern arm.patterns;
          Option.iter visit.expression arm.guard;
          walk_block visit arm.body)
        arms
  | Block body -> walk_block visit body
  | Provide { implementations; body } ->
      List.iter
        (fun (implementation : Core.implementation) -> walk_operand visit implementation.value)
        implementations;
      walk_block visit body
  | Return value -> Option.iter visit.expression value
  | Quantified { binder; body; _ } ->
      (match binder with
      | Over_type _ -> ()
      | Over_range { pattern; start; stop; _ } ->
          visit.expression start;
          visit.expression stop;
          visit.pattern pattern
      | Over_elements { pattern; elements = { count; position; element } } ->
          visit.expression count;
          visit.pattern position;
          walk_place visit element;
          visit.pattern pattern);
      visit.expression body

let walk_statement_children visit (node : Core.statement) =
  match node.kind with
  | Let { pattern; value; else_ } ->
      walk_operand visit value;
      visit.pattern pattern;
      Option.iter (walk_block visit) else_
  | Evaluate value -> visit.expression value
  | Assign { target; value } ->
      walk_place visit target;
      visit.expression value
  | Compound_assign { target; operand = right; value; _ } ->
      walk_operand visit right;
      walk_place visit target;
      visit.expression value
  | For { pattern; iteration; clauses; body; _ } ->
      (match iteration with
      | Integer_range { start; stop; _ } ->
          visit.expression start;
          visit.expression stop
      | Elements { count; position; element } ->
          visit.expression count;
          visit.pattern position;
          walk_place visit element
      | Cursor { cursor; next } ->
          walk_place visit cursor;
          visit.callee next);
      visit.pattern pattern;
      List.iter (walk_loop_clause visit) clauses;
      walk_block visit body
  | While { condition; clauses; body; _ } ->
      visit.expression condition;
      List.iter (walk_loop_clause visit) clauses;
      walk_block visit body
  | Parallel branches | Concurrent branches -> List.iter visit.statement branches
  | Proof body -> walk_block visit body
  | Assert { condition = { value; _ }; _ } -> visit.expression value
  | Yield { part; _ } -> walk_operand visit part

let walk_pattern_children visit (node : Core.pattern) =
  match node.kind with
  | Wildcard | Bind _ | Literal _ | Range _ -> ()
  | Variant { fields; _ } | Record fields ->
      List.iter (fun (_, inner) -> visit.pattern inner) fields
  | Equal_to { equal; _ } -> visit.callee equal
  | Alternatives alternatives -> List.iter visit.pattern alternatives

let rec make_deep_visitor visit =
  {
    expression =
      (fun node ->
        visit.expression node;
        walk_expression_children (make_deep_visitor visit) node);
    statement =
      (fun node ->
        visit.statement node;
        walk_statement_children (make_deep_visitor visit) node);
    pattern =
      (fun node ->
        visit.pattern node;
        walk_pattern_children (make_deep_visitor visit) node);
    callee = visit.callee;
    place = visit.place;
  }

let walk_expression visit node = (make_deep_visitor visit).expression node

let walk_parameter visit (parameter : Core.parameter) =
  Option.iter visit.expression parameter.default;
  Option.iter
    (fun (contract : Core.callback_contract) -> List.iter visit.expression contract.requires)
    parameter.callback_contract

let walk_definition_children visit = function
  | Core.Function { parameters; contract; body } ->
      List.iter (walk_parameter visit) parameters;
      List.iter
        (fun (condition : Core.condition) -> visit.expression condition.value)
        contract.requires;
      List.iter visit.expression contract.ensures;
      List.iter visit.expression contract.decreases;
      List.iter (walk_cost visit) contract.costs;
      Option.iter (walk_block visit) body
  | Type { defaults; invariants; potential } ->
      List.iter (fun (_, _, value) -> visit.expression value) defaults;
      List.iter (fun (invariant : Core.condition) -> visit.expression invariant.value) invariants;
      Option.iter visit.expression potential
  | Trait laws ->
      List.iter
        (fun (law : Core.law) ->
          List.iter (walk_parameter visit) law.parameters;
          List.iter visit.expression law.requires;
          walk_block visit law.body)
        laws
  | Constant value -> Option.iter visit.expression value
  | Test body | Law_proof { body; _ } -> Option.iter (walk_block visit) body
  | Empty -> ()

let walk_definition visit core_definition =
  walk_definition_children (make_deep_visitor visit) core_definition

let is_functional walk =
  let fine = ref true in
  let rec visit =
    {
      ignore_all with
      expression =
        (fun (node : Core.expression) ->
          match node.kind with
          | Return _ | Break | Continue | Todo | Echo _ | Provide _ | Unreachable -> fine := false
          | _ when node.type_ = Types.Never -> fine := false
          | Call { arguments; _ } ->
              if
                List.exists
                  (function
                    | Core.Passed { mode = Types.Mut; _ } -> true
                    | Core.Passed _ | Core.Default -> false)
                  arguments
              then fine := false;
              walk_expression_children visit node
          | _ -> walk_expression_children visit node);
      statement =
        (fun (node : Core.statement) ->
          match node.kind with
          | Let { pattern; else_ = None; _ } when not (binds_variable pattern) ->
              walk_statement_children visit node
          | Evaluate _ -> walk_statement_children visit node
          | _ -> fine := false);
      pattern = (fun node -> walk_pattern_children visit node);
    }
  and binds_variable (pattern : Core.pattern) =
    let child_binds = ref false in
    walk_pattern_children
      { ignore_all with pattern = (fun inner -> if binds_variable inner then child_binds := true) }
      pattern;
    !child_binds || match pattern.kind with Bind { is_var; _ } -> is_var | _ -> false
  in
  walk visit;
  !fine

let has_implicit_measure (condition : Core.expression) =
  match condition.kind with
  | Compare { comparison = Less | Less_equal | Greater | Greater_equal; left; right } ->
      is_functional (fun visit -> walk_expression visit left)
      && is_functional (fun visit -> walk_expression visit right)
  | _ -> false

type tasks_use = Uses_tasks | Through_parameter | No_tasks

let compute_tasks_use ?(read_solved = fun (_ : int) : Types.capability_set -> Types.no_capabilities)
    (body : Core.block) : tasks_use =
  let usage = ref No_tasks in
  let rec mark_used (capability : Types.capability) =
    match capability with
    | Capability path -> if Path.equal path (Well_known.make_path Tasks) then usage := Uses_tasks
    | Capability_parameter _ | Capability_projection _ ->
        if !usage = No_tasks then usage := Through_parameter
    | Capability_variable variable ->
        List.iter mark_used (read_solved variable :> Types.capability list)
    | Capability_error _ ->
        Compiler_bug.raise_bug ~stage:"Core_walk" "a core form uses a capability with an error"
    | Divergence _ -> ()
  in
  walk_block
    (make_deep_visitor
       {
         ignore_all with
         expression =
           (fun node ->
             match node.kind with
             | Call call -> List.iter mark_used (call.uses :> Types.capability list)
             | _ -> ());
         statement =
           (fun node ->
             match node.kind with
             | Concurrent _ | For { mode = Concurrent_loop; _ } -> usage := Uses_tasks
             | For { mode = Sequential | Parallel_loop; _ }
             | Let _ | Evaluate _ | Assign _ | Compound_assign _ | While _ | Parallel _ | Proof _
             | Assert _ | Yield _ ->
                 ());
       })
    body;
  !usage

let can_use_tasks (body : Core.block) : bool = compute_tasks_use body <> No_tasks

let traverse_indirect (change : 'a -> 'b option) : 'a Core.target -> 'b Core.target option =
  function
  | Function { path; type_arguments } -> Some (Function { path; type_arguments })
  | Trait_method { trait; name; receiver; self_type; type_arguments; evidence } ->
      Some (Trait_method { trait; name; receiver; self_type; type_arguments; evidence })
  | Capability_method { capability; name } -> Some (Capability_method { capability; name })
  | Intrinsic { operation; type_arguments } -> Some (Intrinsic { operation; type_arguments })
  | Indirect value -> Option.map (fun value -> Core.Indirect value) (change value)

let find_local_name : Core.local -> string option = function
  | Declared { name; _ } | Trait_parameter { name; _ } -> Some name
  | Self -> Some "self"
  | Synthetic _ -> None

module For_testing = struct
  exception Found

  let expression_exists is_wanted node =
    let visit =
      make_deep_visitor
        { ignore_all with expression = (fun node -> if is_wanted node then raise Found) }
    in
    match visit.expression node with () -> false | exception Found -> true
end

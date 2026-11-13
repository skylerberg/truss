open Core

type visit = {
  expression : expression -> unit;
  statement : statement -> unit;
  pattern : pattern -> unit;
  callee : callee -> unit;
  place : place -> unit;
}

let ignore_all =
  { expression = ignore; statement = ignore; pattern = ignore; callee = ignore; place = ignore }

let callees on_callee =
  {
    ignore_all with
    expression =
      (fun node -> match node.kind with Call { callee; _ } -> on_callee callee | _ -> ());
    callee = on_callee;
  }

let place_type : place -> Types.ty = function
  | Local { type_; _ } | Constant { type_; _ } | Field { type_; _ } -> type_
  | Lent value | Temporary value -> value.type_

let place_origin : place -> origin = function
  | Local { origin; _ } | Constant { origin; _ } | Field { origin; _ } -> origin
  | Lent value | Temporary value -> value.origin

let rec lent_places : operand -> place list = function
  | Place core_place -> [ core_place ]
  | Value { kind = Construct { fields; _ }; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:lent_places field) fields
  | Value _ -> []

let rec place visit core_place =
  visit.place core_place;
  match core_place with
  | Local _ | Constant _ -> ()
  | Field { base; _ } -> place visit base
  | Lent call -> visit.expression call
  | Temporary value -> visit.expression value

let operand visit = function
  | Place core_place -> place visit core_place
  | Value value -> visit.expression value

let block visit (body : block) =
  List.iter visit.statement body.statements;
  Option.iter visit.expression body.value

let cost visit (cost : cost) =
  match cost.bound with
  | Finite -> ()
  | Order_of value | At_most value | Exactly value -> visit.expression value

let loop_clause visit = function
  | Invariant value -> visit.expression value
  | Decreases measures -> List.iter visit.expression measures
  | Cost bound -> cost visit bound

let expression_children visit (node : expression) =
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Value_parameter _ | Break
  | Continue | Todo | Unreachable | Result | Current_target | Yielded | Finished
  (* The callee of a [Method_time] is not called, so it is not reported to
     the visitor. *)
  | Method_time _ ->
      ()
  | Template { call; _ } -> visit.expression call
  | Use core_place -> place visit core_place
  | Copy value -> operand visit value
  | Lambda { parameters; body; _ } ->
      List.iter visit.pattern parameters;
      block visit body
  | Construct { fields; _ } ->
      List.iter (fun (_, value) -> Option.iter (operand visit) value) fields
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
  (* [base] is the first argument of [call], so the call covers it. *)
  | Slice { call; _ } -> visit.expression call
  | Call call ->
      (match call.callee with
      | Indirect function_value -> operand visit function_value
      | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ());
      List.iter
        (function Passed { value; _ } -> operand visit value | Default -> ())
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
      operand visit value;
      visit.pattern pattern
  | Cursor_next cursor -> place visit cursor
  | Convert { value; _ } -> visit.expression value
  | If { condition; then_; else_; _ } ->
      visit.expression condition;
      block visit then_;
      Option.iter (block visit) else_
  | Match { scrutinees; arms; _ } ->
      List.iter (operand visit) scrutinees;
      List.iter
        (fun (arm : arm) ->
          List.iter visit.pattern arm.patterns;
          Option.iter visit.expression arm.guard;
          block visit arm.body)
        arms
  | Block body -> block visit body
  | Provide { implementations; body } ->
      List.iter
        (fun (implementation : implementation) -> operand visit implementation.value)
        implementations;
      block visit body
  | Return value -> Option.iter visit.expression value
  | Quantified { binder; body; _ } ->
      (match binder with
      | Over_type _ -> ()
      | Over_range { pattern; start; stop; _ } ->
          visit.expression start;
          visit.expression stop;
          visit.pattern pattern
      | Over_collection { pattern; collection } | Over_each { pattern; call = collection } ->
          visit.expression collection;
          visit.pattern pattern);
      visit.expression body

let statement_children visit (node : statement) =
  match node.kind with
  | Let { pattern; value; else_ } ->
      operand visit value;
      visit.pattern pattern;
      Option.iter (block visit) else_
  | Evaluate value -> visit.expression value
  | Assign { target; value } ->
      place visit target;
      visit.expression value
  | Compound_assign { target; operand = right; value; _ } ->
      operand visit right;
      place visit target;
      visit.expression value
  | For { pattern; iteration; clauses; body; _ } ->
      (match iteration with
      | Integer_range { start; stop; _ } ->
          visit.expression start;
          visit.expression stop
      | Yielding_call call -> visit.expression call
      | Cursor { cursor; next } ->
          place visit cursor;
          Option.iter visit.callee next);
      visit.pattern pattern;
      List.iter (loop_clause visit) clauses;
      block visit body
  | While { condition; clauses; body; _ } ->
      visit.expression condition;
      List.iter (loop_clause visit) clauses;
      block visit body
  | Parallel branches | Concurrent branches -> List.iter visit.statement branches
  | Proof body -> block visit body
  | Assert { condition = { value; _ }; _ } -> visit.expression value
  | Yield { part; _ } -> operand visit part

let pattern_children visit (node : pattern) =
  match node.kind with
  | Wildcard | Bind _ -> ()
  | Variant { fields; _ } | Record fields ->
      List.iter (fun (_, inner) -> visit.pattern inner) fields
  | Literal value -> visit.expression value
  | Range { start; stop; _ } ->
      visit.expression start;
      visit.expression stop
  | Equal_to { value; equal } ->
      visit.expression value;
      visit.callee equal
  | Alternatives alternatives -> List.iter visit.pattern alternatives

let rec deep visit =
  {
    expression =
      (fun node ->
        visit.expression node;
        expression_children (deep visit) node);
    statement =
      (fun node ->
        visit.statement node;
        statement_children (deep visit) node);
    pattern =
      (fun node ->
        visit.pattern node;
        pattern_children (deep visit) node);
    callee = visit.callee;
    place = visit.place;
  }

let expression visit node = (deep visit).expression node

exception Found

let exists walk ?(expression = fun _ -> false) ?(statement = fun _ -> false) node =
  let test check node = if check node then raise Found in
  let visit = deep { ignore_all with expression = test expression; statement = test statement } in
  match walk visit node with () -> false | exception Found -> true

let block_exists ?expression ?statement node = exists block ?expression ?statement node

let expression_exists ?expression ?statement node =
  exists (fun visit -> visit.expression) ?expression ?statement node

let statement_exists ?expression ?statement node =
  exists (fun visit -> visit.statement) ?expression ?statement node

let parameter visit (parameter : parameter) =
  Option.iter visit.expression parameter.default;
  Option.iter
    (fun (contract : callback_contract) -> List.iter visit.expression contract.requires)
    parameter.callback_contract

let definition_children visit = function
  | Function { parameters; contract; body } ->
      List.iter (parameter visit) parameters;
      List.iter (fun (condition : condition) -> visit.expression condition.value) contract.requires;
      List.iter visit.expression contract.ensures;
      List.iter visit.expression contract.decreases;
      List.iter (cost visit) contract.costs;
      Option.iter (block visit) body
  | Type { defaults; invariants; potential } ->
      List.iter (fun (_, _, value) -> visit.expression value) defaults;
      List.iter visit.expression invariants;
      Option.iter visit.expression potential
  | Trait laws ->
      List.iter
        (fun (law : law) ->
          List.iter (parameter visit) law.parameters;
          List.iter visit.expression law.requires;
          block visit law.body)
        laws
  | Constant value -> visit.expression value
  | Test body | Law_proof { body; _ } -> block visit body
  | Empty -> ()

let definition visit core_definition = definition_children (deep visit) core_definition

type tasks_use = Uses_tasks | Through_parameter | No_tasks

let tasks_use ?(solved = fun (_ : int) : Types.capability_set -> Types.no_capabilities)
    (body : block) : tasks_use =
  let usage = ref No_tasks in
  let rec used (capability : Types.capability) =
    match capability with
    | Capability path -> if Path.equal path (Well_known.path Tasks) then usage := Uses_tasks
    | Capability_parameter _ | Capability_projection _ ->
        if !usage = No_tasks then usage := Through_parameter
    | Capability_variable variable -> List.iter used (solved variable :> Types.capability list)
  in
  block
    (deep
       {
         ignore_all with
         expression =
           (fun node ->
             match node.kind with
             | Call call -> List.iter used (call.uses :> Types.capability list)
             | _ -> ());
         statement =
           (fun node ->
             match node.kind with
             | Concurrent _ | For { mode = Concurrent_loop; _ } -> usage := Uses_tasks
             | _ -> ());
       })
    body;
  !usage

let can_use_tasks ?solved (body : block) : bool = tasks_use ?solved body <> No_tasks

(* A [List], a [Slice], or an [Array]. An element of one of these is a
   place. An index of any other collection is a call of the collection's
   [at], which lends the element. *)
let is_storage type_ =
  Types.is_well_known List type_ || Types.is_well_known Slice type_ || Types.is_builtin Array type_

(* If the expression is an index of a [List], a [Slice], or an [Array],
   the collection that is indexed. *)
let storage_index (value : expression) : place option =
  match value.kind with
  | Call
      {
        callee = Trait_method { trait; name = "at"; self_type; _ };
        arguments = Passed { value = Place collection; _ } :: _;
        _;
      }
    when Well_known.is Index trait.trait && is_storage self_type ->
      Some collection
  | _ -> None

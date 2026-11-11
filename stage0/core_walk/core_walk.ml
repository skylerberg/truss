(* Traversal of the core form.

   A visitor is a record of callbacks. The [*_children] functions call the
   visitor on the direct children of one node, and do not recurse. [deep]
   turns a visitor into one that recurses into every descendant. *)

open Core

(* [callee] is called for every callee that is stored in a node other than
   a [Call]: an interpolated piece's [display], a cursor's [next], and a
   pattern's [equal]. The
   callee of a [Call] is not reported here, because the visitor sees the
   [Call] node itself. *)
type visit = {
  expression : expression -> unit;
  statement : statement -> unit;
  pattern : pattern -> unit;
  callee : callee -> unit;
}

let ignore_all = { expression = ignore; statement = ignore; pattern = ignore; callee = ignore }

(* A visitor that calls [found] on every callee: the callee of each [Call],
   and each callee that is stored in another node. *)
let callees found =
  {
    ignore_all with
    expression = (fun node -> match node.kind with Call { callee; _ } -> found callee | _ -> ());
    callee = found;
  }

let place_type : place -> Types.ty = function
  | Local { type_; _ } | Constant { type_; _ } | Field { type_; _ } -> type_
  | Lent value | Temporary value -> value.type_

let place_origin : place -> origin = function
  | Local { origin; _ } | Constant { origin; _ } | Field { origin; _ } -> origin
  | Lent value | Temporary value -> value.origin

(* The places that a yielded operand lends: the operand itself if it is a
   place, and the fields of a yielded construct that are places, to any
   depth. *)
let rec lent_places : operand -> place list = function
  | Place found -> [ found ]
  | Value { kind = Construct { fields; _ }; _ } ->
      List.concat_map (fun (_, field) -> Option.fold ~none:[] ~some:lent_places field) fields
  | Value _ -> []

let rec place visit = function
  | Local _ | Constant _ -> ()
  | Field { base; _ } -> place visit base
  | Lent call -> visit.expression call
  | Temporary value -> visit.expression value

let operand visit = function
  | Place found -> place visit found
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
  | Interpolated { pieces; builder_new; builder_write; builder_finish } ->
      visit.callee builder_new;
      List.iter
        (function
          | Text _ -> ()
          | Displayed { value; display } ->
              operand visit value;
              visit.callee display)
        pieces;
      visit.callee builder_write;
      visit.callee builder_finish
  | Template { call; _ } -> visit.expression call
  | Use found -> place visit found
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
  | If { condition; then_; else_ } ->
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
  | Task_exit { exit; _ } -> visit.expression exit
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
  | Assign { target; value } | Compound_assign { target; value } ->
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
  | While { condition; clauses; body } ->
      visit.expression condition;
      List.iter (loop_clause visit) clauses;
      block visit body
  | Parallel branches | Concurrent branches -> List.iter visit.statement branches
  | Proof body -> block visit body
  | Assert { value; _ } -> visit.expression value
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

(* A visitor that calls [visit] on a node and then on all of its
   descendants, in evaluation order. *)
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
  }

(* Calls [visit] on an expression and all of its descendants. *)
let expression visit node = (deep visit).expression node

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
  | Test body | Law_proof body -> block visit body
  | Empty -> ()

(* Calls [visit] on every node of a definition. *)
let definition visit found = definition_children (deep visit) found
let tasks_capability = Well_known.path Tasks

(* How code can use [Tasks]. *)
type tasks_use =
  | Uses_tasks  (** It contains [concurrent] code, or a call in it uses [Tasks]. *)
  | Through_parameter
      (** A call in it uses a capability parameter, which may be instantiated with [Tasks]. *)
  | No_tasks

(* How code can use [Tasks]. [solved] gives the solution of a capability
   variable, for a core form whose capability variables are not solved yet. *)
let tasks_use ?(solved = fun (_ : int) : Types.capability list -> []) (body : block) : tasks_use =
  let found = ref No_tasks in
  let rec used (capability : Types.capability) =
    match capability with
    | Capability path -> if Path.equal path tasks_capability then found := Uses_tasks
    | Capability_parameter _ -> if !found = No_tasks then found := Through_parameter
    | Capability_variable variable -> List.iter used (solved variable)
  in
  block
    (deep
       {
         ignore_all with
         expression =
           (fun node -> match node.kind with Call call -> List.iter used call.uses | _ -> ());
         statement =
           (fun node ->
             match node.kind with
             | Concurrent _ | For { mode = Concurrent_loop; _ } -> found := Uses_tasks
             | _ -> ());
       })
    body;
  !found

(* Whether code can use [Tasks]. An implementation that is provided [mut]
   around such code is a monitor. *)
let can_use_tasks ?solved (body : block) : bool = tasks_use ?solved body <> No_tasks

(* Whether a yielding method yields by position: its body is one [for] loop
   over a range of integers, and the loop body is one [yield]. The
   iterations share no state, so a [parallel for] or a [concurrent for] over
   the method can run the range loop's iterations at the same time. *)
let yields_by_position (body : block) : bool =
  match (body.statements, body.value) with
  | ( [
        {
          kind =
            For
              {
                iteration = Integer_range _;
                body = { statements = [ { kind = Yield _; _ } ]; value = None; _ };
                _;
              };
          _;
        };
      ],
      None ) ->
      true
  | _ -> false

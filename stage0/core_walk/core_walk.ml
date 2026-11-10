(* Traversal of the core form.

   A visitor is a record of callbacks. The [*_children] functions call the
   visitor on the direct children of one node, and do not recurse. [deep]
   turns a visitor into one that recurses into every descendant. *)

open Core

(* [callee] is called for every callee that is stored in a node other than
   a [Call]: an interpolated piece's [display], a collection literal's
   [empty] and [insert], a cursor's [next], and a pattern's [equal]. The
   callee of a [Call] is not reported here, because the visitor sees the
   [Call] node itself. *)
type visit = {
  expression : expression -> unit;
  statement : statement -> unit;
  pattern : pattern -> unit;
  callee : callee -> unit;
}

let ignore_all = { expression = ignore; statement = ignore; pattern = ignore; callee = ignore }

let rec place visit = function
  | Local _ -> ()
  | Field { base; _ } -> place visit base
  | Lent call -> visit.expression call
  | Temporary value -> visit.expression value

let operand visit = function
  | Place found -> place visit found
  | Value value -> visit.expression value

let block visit (body : block) =
  List.iter visit.statement body.statements;
  Option.iter visit.expression body.value

let construction visit = function
  | Array | Specification_only -> ()
  | By_insertion { empty; insert } ->
      visit.callee empty;
      visit.callee insert

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
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Constant _ | Value_parameter _
  | Break | Continue | Todo | Unreachable | Result | Current_target | Yielded | Finished ->
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
      List.iter (fun (_, value) -> Option.iter visit.expression value) fields
  | Collection_literal { elements; construction = how } ->
      List.iter visit.expression elements;
      construction visit how
  | Map_literal { entries; construction = how } ->
      List.iter
        (fun (key, value) ->
          visit.expression key;
          visit.expression value)
        entries;
      construction visit how
  | Record_update { base; updates } ->
      visit.expression base;
      List.iter (fun (_, value) -> visit.expression value) updates
  | Slice { base; start; stop; _ } ->
      place visit base;
      Option.iter visit.expression start;
      Option.iter visit.expression stop
  | Call call ->
      (match call.callee with
      | Indirect function_value -> operand visit function_value
      | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ());
      List.iter
        (function Passed { value; _ } -> operand visit value | Default -> ())
        call.arguments
  | Operator { arguments; _ } | Cost_function { arguments; _ } ->
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
  | Quantified { binder; body; _ } ->
      (match binder with
      | Over_type _ -> ()
      | Over_range { pattern; start; stop; _ } ->
          visit.expression start;
          visit.expression stop;
          visit.pattern pattern
      | Over_collection { pattern; collection } ->
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
  | Parallel branches -> List.iter visit.statement branches
  | Proof body -> block visit body
  | Assert { value; _ } -> visit.expression value
  | Yield { part; _ } -> operand visit part

let pattern_children visit (node : pattern) =
  match node.kind with
  | Wildcard | Bind _ -> ()
  | Variant { fields; _ } | Record fields -> List.iter (fun (_, inner) -> visit.pattern inner) fields
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

(* Walking the core form: every node inside a node, in the order they are
   worked out. *)

open Core

type visit = {
  expression : expression -> unit;
  statement : statement -> unit;
  pattern : pattern -> unit;
}

let rec expression visit (node : expression) =
  visit.expression node;
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Constant _ | Generic_value _
  | Break | Continue | Todo | Unreachable | Result | Updating | Yielded | Finished ->
      ()
  | Interpolated { pieces; start; write; finish } ->
      callee visit start;
      List.iter
        (function
          | Text _ -> ()
          | Displayed { value; display } ->
              expression visit value;
              callee visit display)
        pieces;
      callee visit write;
      callee visit finish
  | Template { from_template; template } ->
      expression visit template;
      callee visit from_template
  | Use found -> place visit found
  | Copy given -> operand visit given
  | Lambda { parameters; body; _ } ->
      List.iter (pattern visit) parameters;
      block visit body
  | Construct { fields; _ } ->
      List.iter (fun (_, given) -> Option.iter (expression visit) given) fields
  | Collection { elements; built } ->
      List.iter (expression visit) elements;
      collection visit built
  | Entries { entries; built } ->
      List.iter
        (fun (key, value) ->
          expression visit key;
          expression visit value)
        entries;
      collection visit built
  | Updated { base; updates } ->
      expression visit base;
      List.iter (fun (_, value) -> expression visit value) updates
  | Slice { base; start; stop; _ } ->
      place visit base;
      Option.iter (expression visit) start;
      Option.iter (expression visit) stop
  | Call made -> call visit made
  | Operator { arguments; _ } | Measure { arguments; _ } -> List.iter (expression visit) arguments
  | Compare { left; right; _ }
  | Both (left, right)
  | Either (left, right)
  | Implies (left, right)
  | Identical (left, right) ->
      expression visit left;
      expression visit right
  | Not inner | Echo inner | Old inner | Any { value = inner; _ } -> expression visit inner
  | Matches { value; pattern = matched } ->
      operand visit value;
      pattern visit matched
  | Next cursor -> place visit cursor
  | Convert { conversion; value } -> (
      expression visit value;
      match conversion with
      | View view -> callee visit view
      | Widen | To_integer | From_integer -> ())
  | If { condition; then_; else_ } ->
      expression visit condition;
      block visit then_;
      Option.iter (block visit) else_
  | Match { scrutinees; arms; _ } ->
      List.iter (operand visit) scrutinees;
      List.iter
        (fun (arm : arm) ->
          List.iter (pattern visit) arm.patterns;
          Option.iter (expression visit) arm.guard;
          block visit arm.body)
        arms
  | Block body -> block visit body
  | Provide { implementations; body } ->
      List.iter
        (fun (implementation : implementation) -> operand visit implementation.value)
        implementations;
      block visit body
  | Return value -> Option.iter (expression visit) value
  | Quantified { binder = bound; body; _ } ->
      (match bound with
      | Over_type _ -> ()
      | Over_range { pattern = matched; start; stop; _ } ->
          expression visit start;
          expression visit stop;
          pattern visit matched
      | Over_collection { pattern = matched; collection } ->
          expression visit collection;
          pattern visit matched);
      expression visit body

and callee visit = function
  | Value function_ -> expression visit function_
  | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ()

and collection visit = function
  | Array | Modelled -> ()
  | From_storage from -> callee visit from
  | Inserted { empty; insert } ->
      callee visit empty;
      callee visit insert

and call visit (made : call) =
  callee visit made.callee;
  List.iter (function Passed { value; _ } -> operand visit value | Default -> ()) made.arguments

and operand visit = function
  | Place found -> place visit found
  | Value value -> expression visit value

and place visit = function
  | Local _ -> ()
  | Field { base; _ } -> place visit base
  | Lent lending -> expression visit lending
  | Temporary value -> expression visit value

and block visit (body : block) =
  List.iter (statement visit) body.statements;
  Option.iter (expression visit) body.value

and statement visit (node : statement) =
  visit.statement node;
  match node.kind with
  | Let { pattern = bound; value; otherwise } ->
      operand visit value;
      pattern visit bound;
      Option.iter (block visit) otherwise
  | Evaluate value -> expression visit value
  | Assign { target; value } | Update { target; value } ->
      place visit target;
      expression visit value
  | For { pattern = bound; drive = over; clauses; body; _ } ->
      (match over with
      | Count { start; stop; _ } ->
          expression visit start;
          expression visit stop
      | Each each -> expression visit each
      | Pull { cursor; next } ->
          expression visit cursor;
          Option.iter (callee visit) next);
      pattern visit bound;
      List.iter (loop_clause visit) clauses;
      block visit body
  | While { condition; clauses; body } ->
      expression visit condition;
      List.iter (loop_clause visit) clauses;
      block visit body
  | Parallel branches -> List.iter (statement visit) branches
  | Proof body -> block visit body
  | Assert { value; _ } -> expression visit value
  | Yield { part; _ } -> operand visit part

and loop_clause visit = function
  | Invariant value -> expression visit value
  | Decreases measures -> List.iter (expression visit) measures
  | Cost spent -> cost visit spent

and cost visit (spent : cost) =
  match spent.bound with
  | Finite -> ()
  | Order_of value | At_most value | Exactly value -> expression visit value

and pattern visit (node : pattern) =
  visit.pattern node;
  match node.kind with
  | Anything | Bind _ -> ()
  | Variant { fields; _ } | Record fields ->
      List.iter (fun (_, inner) -> pattern visit inner) fields
  | Literal value -> expression visit value
  | Within { start; stop; _ } ->
      expression visit start;
      expression visit stop
  | Equals { value; equal } ->
      expression visit value;
      callee visit equal
  | Alternatives alternatives -> List.iter (pattern visit) alternatives

let nothing = { expression = ignore; statement = ignore; pattern = ignore }

let parameter visit (written : parameter) =
  Option.iter (expression visit) written.default;
  Option.iter
    (fun (accepted : accepts) -> List.iter (expression visit) accepted.requires)
    written.accepts

let parts visit = function
  | Function { parameters; contract; body } ->
      List.iter (parameter visit) parameters;
      List.iter (fun (clause : clause) -> expression visit clause.value) contract.requires;
      List.iter (expression visit) contract.ensures;
      List.iter (expression visit) contract.decreases;
      List.iter (cost visit) contract.costs;
      Option.iter (block visit) body
  | Type { defaults; invariants; potential } ->
      List.iter (fun (_, _, value) -> expression visit value) defaults;
      List.iter (expression visit) invariants;
      Option.iter (expression visit) potential
  | Trait laws ->
      List.iter
        (fun (written : law) ->
          List.iter (parameter visit) written.parameters;
          List.iter (expression visit) written.requires;
          block visit written.body)
        laws
  | Constant value -> expression visit value
  | Test body | Law_proof body -> block visit body
  | Nothing -> ()

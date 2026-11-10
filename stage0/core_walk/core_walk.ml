(* Walking the core form: the nodes directly inside a node, and every node
   inside one, in the order they are worked out. *)

open Core

(* What is done with each node met. [callee] is given what is called
   without being a [Call] of its own: a piece's [display], a view's method,
   what builds a collection. *)
type visit = {
  expression : expression -> unit;
  statement : statement -> unit;
  pattern : pattern -> unit;
  callee : callee -> unit;
}

let nothing = { expression = ignore; statement = ignore; pattern = ignore; callee = ignore }

let rec place visit = function
  | Local _ -> ()
  | Field { base; _ } -> place visit base
  | Lent lending -> visit.expression lending
  | Temporary value -> visit.expression value

let operand visit = function
  | Place found -> place visit found
  | Value value -> visit.expression value

let block visit (body : block) =
  List.iter visit.statement body.statements;
  Option.iter visit.expression body.value

let collection visit = function
  | Array | Modelled -> ()
  | From_storage from -> visit.callee from
  | Inserted { empty; insert } ->
      visit.callee empty;
      visit.callee insert

let cost visit (spent : cost) =
  match spent.bound with
  | Finite -> ()
  | Order_of value | At_most value | Exactly value -> visit.expression value

let loop_clause visit = function
  | Invariant value -> visit.expression value
  | Decreases measures -> List.iter visit.expression measures
  | Cost spent -> cost visit spent

(* The nodes directly inside an expression. *)
let expression_parts visit (node : expression) =
  match node.kind with
  | Integer _ | Float _ | Boolean _ | String _ | Function_value _ | Constant _ | Generic_value _
  | Break | Continue | Todo | Unreachable | Result | Updating | Yielded | Finished ->
      ()
  | Interpolated { pieces; start; write; finish } ->
      visit.callee start;
      List.iter
        (function
          | Text _ -> ()
          | Displayed { value; display } ->
              visit.expression value;
              visit.callee display)
        pieces;
      visit.callee write;
      visit.callee finish
  | Template { from_template; template } ->
      visit.expression template;
      visit.callee from_template
  | Use found -> place visit found
  | Copy given -> operand visit given
  | Lambda { parameters; body; _ } ->
      List.iter visit.pattern parameters;
      block visit body
  | Construct { fields; _ } ->
      List.iter (fun (_, given) -> Option.iter visit.expression given) fields
  | Collection { elements; built } ->
      List.iter visit.expression elements;
      collection visit built
  | Entries { entries; built } ->
      List.iter
        (fun (key, value) ->
          visit.expression key;
          visit.expression value)
        entries;
      collection visit built
  | Updated { base; updates } ->
      visit.expression base;
      List.iter (fun (_, value) -> visit.expression value) updates
  | Slice { base; start; stop; _ } ->
      place visit base;
      Option.iter visit.expression start;
      Option.iter visit.expression stop
  | Call made ->
      (match made.callee with
      | Value function_ -> visit.expression function_
      | Function _ | Trait_method _ | Capability_method _ | Intrinsic _ -> ());
      List.iter
        (function Passed { value; _ } -> operand visit value | Default -> ())
        made.arguments
  | Operator { arguments; _ } | Measure { arguments; _ } -> List.iter visit.expression arguments
  | Compare { left; right; _ }
  | Both (left, right)
  | Either (left, right)
  | Implies (left, right)
  | Identical (left, right) ->
      visit.expression left;
      visit.expression right
  | Not inner | Echo inner | Old inner | Any { value = inner; _ } -> visit.expression inner
  | Matches { value; pattern = matched } ->
      operand visit value;
      visit.pattern matched
  | Next cursor -> place visit cursor
  | Convert { conversion; value } -> (
      visit.expression value;
      match conversion with
      | View view -> visit.callee view
      | Widen | To_integer | From_integer -> ())
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
  | Quantified { binder = bound; body; _ } ->
      (match bound with
      | Over_type _ -> ()
      | Over_range { pattern = matched; start; stop; _ } ->
          visit.expression start;
          visit.expression stop;
          visit.pattern matched
      | Over_collection { pattern = matched; collection } ->
          visit.expression collection;
          visit.pattern matched);
      visit.expression body

(* The nodes directly inside a statement. *)
let statement_parts visit (node : statement) =
  match node.kind with
  | Let { pattern = bound; value; otherwise } ->
      operand visit value;
      visit.pattern bound;
      Option.iter (block visit) otherwise
  | Evaluate value -> visit.expression value
  | Assign { target; value } | Update { target; value } ->
      place visit target;
      visit.expression value
  | For { pattern = bound; drive = over; clauses; body; _ } ->
      (match over with
      | Count { start; stop; _ } ->
          visit.expression start;
          visit.expression stop
      | Each each -> visit.expression each
      | Pull { cursor; next } ->
          visit.expression cursor;
          Option.iter visit.callee next);
      visit.pattern bound;
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

(* The nodes directly inside a pattern. *)
let pattern_parts visit (node : pattern) =
  match node.kind with
  | Anything | Bind _ -> ()
  | Variant { fields; _ } | Record fields ->
      List.iter (fun (_, inner) -> visit.pattern inner) fields
  | Literal value -> visit.expression value
  | Within { start; stop; _ } ->
      visit.expression start;
      visit.expression stop
  | Equals { value; equal } ->
      visit.expression value;
      visit.callee equal
  | Alternatives alternatives -> List.iter visit.pattern alternatives

(* Every node inside, each given to [visit] before what is inside it. *)
let rec every visit =
  {
    expression =
      (fun node ->
        visit.expression node;
        expression_parts (every visit) node);
    statement =
      (fun node ->
        visit.statement node;
        statement_parts (every visit) node);
    pattern =
      (fun node ->
        visit.pattern node;
        pattern_parts (every visit) node);
    callee = visit.callee;
  }

let expression visit node = (every visit).expression node

let parameter visit (written : parameter) =
  Option.iter visit.expression written.default;
  Option.iter
    (fun (accepted : accepts) -> List.iter visit.expression accepted.requires)
    written.accepts

(* The nodes directly inside a definition's parts. *)
let parts_of visit = function
  | Function { parameters; contract; body } ->
      List.iter (parameter visit) parameters;
      List.iter (fun (clause : clause) -> visit.expression clause.value) contract.requires;
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
        (fun (written : law) ->
          List.iter (parameter visit) written.parameters;
          List.iter visit.expression written.requires;
          block visit written.body)
        laws
  | Constant value -> visit.expression value
  | Test body | Law_proof body -> block visit body
  | Nothing -> ()

let parts visit found = parts_of (every visit) found

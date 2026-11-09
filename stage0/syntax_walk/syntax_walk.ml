(* Visiting the expressions of a tree. [children] calls a function on each
   expression directly inside another, including those in the blocks,
   statements, and types it contains; [definition] calls it on each
   outermost expression of a definition. *)

open Syntax

let rec type_expression f (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type f path
  | Any_type path -> path_type f path
  | Function_type { inputs; output; clauses } ->
      List.iter (fun (_, input) -> type_expression f input) inputs;
      Option.iter (type_expression f) output;
      List.iter (clause f) clauses
  | Self_type _ | Associated _ | Type_error -> ()

and path_type f (path : path_type) = List.iter (type_argument f) path.arguments

and type_argument f = function
  | Type_argument type_ | Constraint (_, type_) -> type_expression f type_
  | Count _ | Count_parameter _ -> ()

and clause f (clause : clause) =
  match clause.kind with
  | Uses capabilities -> List.iter (path_type f) capabilities
  | Requires value | Ensures value -> f value
  | Decreases measures -> List.iter f measures
  | Cost cost -> (
      match cost.bound with Big_o value | At_most value | Exactly value -> f value | Finite -> ())
  | Clause_error -> ()

and block f (block : block) = List.iter (statement f) block.statements

and statement f (statement : statement) =
  match statement.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (type_expression f) annotation;
      f value;
      Option.iter (block f) else_
  | Expression value | Assert value | Yield value -> f value
  | Assignment { target; value; _ } ->
      f target;
      f value
  | For { iterable; clauses; body; _ } ->
      f iterable;
      List.iter (loop_clause f) clauses;
      block f body
  | While { condition; clauses; body } ->
      f condition;
      List.iter (loop_clause f) clauses;
      block f body
  | Parallel body | Proof body -> block f body
  | Statement_error -> ()

and loop_clause f (clause : loop_clause) =
  match clause.kind with
  | Invariant value -> f value
  | Loop_decreases measures -> List.iter f measures

and string_literal f (literal : string_literal) = List.iter (fun (value, _) -> f value) literal.rest

let children f (value : expression) =
  match value.kind with
  | Integer _ | Float _ | True | False | Todo | Unreachable | Break | Continue | Self_value
  | Self_type_value | Name _ | Expression_error ->
      ()
  | String literal -> string_literal f literal
  | Member (inner, _)
  | Try inner
  | Prefix (_, inner)
  | Mode (_, inner)
  | Any inner
  | Echo inner
  | Parenthesized inner ->
      f inner
  | Is (inner, _) -> f inner
  | Bracket (inner, items) ->
      f inner;
      List.iter
        (function Item item -> f item | Item_constraint (_, type_) -> type_expression f type_)
        items
  | Call (callee, arguments) ->
      f callee;
      List.iter (fun (argument : argument) -> f argument.value) arguments
  | With (base, updates) ->
      f base;
      List.iter (fun (update : update) -> Option.iter f update.value) updates
  | Binary (_, left, right) ->
      f left;
      f right
  | Range { start; stop; _ } ->
      Option.iter f start;
      Option.iter f stop
  | Quantified { binder; body; _ } ->
      (match binder with
      | Binder_in (_, collection) -> f collection
      | Binder_type (_, type_) -> type_expression f type_);
      f body
  | Return value -> Option.iter f value
  | List items -> List.iter f items
  | Map entries ->
      List.iter
        (fun (key, value) ->
          f key;
          f value)
        entries
  | Lambda { body; _ } -> block f body
  | If { condition; then_; else_ } -> (
      f condition;
      block f then_;
      match else_ with
      | Some (Else body) -> block f body
      | Some (Else_if value) -> f value
      | None -> ())
  | Match { scrutinees; arms } ->
      List.iter f scrutinees;
      List.iter
        (fun (arm : arm) ->
          Option.iter f arm.guard;
          statement f arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter f implementations;
      block f body
  | Block body -> block f body

let generic_parameter f (parameter : generic_parameter) =
  match parameter.kind with
  | Type_parameter (_, bounds) -> List.iter (path_type f) bounds
  | Value_parameter (_, type_) -> type_expression f type_
  | Capability_parameter _ | Generic_error -> ()

let type_head f (head : type_head) = List.iter (generic_parameter f) head.generics
let function_name f = function Plain_name _ -> () | Method_name (head, _) -> type_head f head

let parameter f (parameter : parameter) =
  match parameter.kind with
  | Named_parameter { type_; default; _ } ->
      type_expression f type_;
      Option.iter f default
  | Self_parameter _ | Parameter_error -> ()

let signature f (signature : signature) =
  function_name f signature.name;
  List.iter (generic_parameter f) signature.generics;
  List.iter (parameter f) signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Yields (_, type_)) -> type_expression f type_
  | None -> ());
  List.iter (clause f) signature.clauses

let function_definition f (definition : function_definition) =
  signature f definition.signature;
  Option.iter (block f) definition.body

let field f (field : field) =
  type_expression f field.type_;
  Option.iter f field.default

let definition f (definition : definition) =
  match definition.kind with
  | Function function_ -> function_definition f function_
  | Type_definition { generics; body; clauses; _ } ->
      List.iter (generic_parameter f) generics;
      (match body with
      | Fields fields -> List.iter (field f) fields
      | Variants variants ->
          List.iter
            (fun (variant : variant) -> Option.iter (List.iter (field f)) variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> f value
          | Derives traits -> List.iter (path_type f) traits)
        clauses
  | Trait { generics; requires; members; _ } ->
      List.iter (generic_parameter f) generics;
      List.iter (path_type f) requires;
      List.iter
        (fun (member : trait_member member) ->
          match member.kind with
          | Trait_method function_ -> function_definition f function_
          | Associated_type (_, bounds) -> List.iter (path_type f) bounds
          | Law law ->
              List.iter (parameter f) law.parameters;
              List.iter f law.requires;
              block f law.body
          | Trait_member_error -> ())
        members
  | Impl { trait_; type_; uses; members } ->
      path_type f trait_;
      type_head f type_;
      List.iter (path_type f) uses;
      List.iter
        (fun (member : impl_member member) ->
          match member.kind with
          | Impl_method function_ -> function_definition f function_
          | Associated_definition (_, type_) -> type_expression f type_
          | Impl_member_error -> ())
        members
  | Capability { members; _ } ->
      List.iter
        (fun (member : capability_member member) ->
          match member.kind with
          | Capability_method method_ -> signature f method_
          | Capability_member_error -> ())
        members
  | Constant { name; type_; value } ->
      function_name f name;
      type_expression f type_;
      f value
  | Test { uses; body; _ } ->
      List.iter (path_type f) uses;
      block f body
  | Theorem { generics; parameters; clauses; body; _ } ->
      List.iter (generic_parameter f) generics;
      List.iter (parameter f) parameters;
      List.iter (clause f) clauses;
      block f body
  | Law_proof { trait_; type_; body; _ } ->
      path_type f trait_;
      type_expression f type_;
      block f body
  | Definition_error -> ()

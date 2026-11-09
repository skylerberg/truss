(* Visiting the expressions and statements of a tree.

   [expression_parts] and [statement_parts] visit one level: a node's own
   expressions, including those in the types and clauses it holds, with
   [expression], and the statements of the blocks it holds, with
   [statement]. A walk that needs a context overrides the nodes that change
   it and leaves every other to these, so a construct added to the tree is
   walked by every check without the check listing it. [children],
   [statement], and [block] go all the way down through statements, calling
   one function on expressions; [definition] calls it on each outermost
   expression of a definition. *)

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
  | Count _ | Count_name _ -> ()

and clause f (clause : clause) =
  match clause.kind with
  | Uses capabilities -> List.iter (path_type f) capabilities
  | Requires value | Ensures value -> f value
  | Decreases measures -> List.iter f measures
  | Cost cost -> (
      match cost.bound with Big_o value | At_most value | Exactly value -> f value | Finite -> ())
  | Clause_error -> ()

and loop_clause f (clause : loop_clause) =
  match clause.kind with
  | Invariant value -> f value
  | Loop_decreases measures -> List.iter f measures

and string_literal f (literal : string_literal) = List.iter (fun (value, _) -> f value) literal.rest

let expression_parts ~expression:f ~statement (value : expression) =
  let block (block : block) = List.iter statement block.statements in
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
  | Is { value = inner; _ } -> f inner
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
      List.iter
        (fun (update : update) ->
          match update.kind with Update { value; _ } -> Option.iter f value | Update_error -> ())
        updates
  | Binary { left; right; _ } ->
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
  | Lambda { body; _ } -> block body
  | If { condition; then_; else_ } -> (
      f condition;
      block then_;
      match else_ with
      | Some (Else body) -> block body
      | Some (Else_if value) -> f value
      | None -> ())
  | Match { scrutinees; arms } ->
      List.iter f scrutinees;
      List.iter
        (fun (arm : arm) ->
          Option.iter f arm.guard;
          statement arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter f implementations;
      block body
  | Block body -> block body

let statement_parts ~expression:f ~statement (written : statement) =
  let block (block : block) = List.iter statement block.statements in
  match written.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (type_expression f) annotation;
      f value;
      Option.iter block else_
  | Expression value | Assert value | Yield value -> f value
  | Assignment { target; value; _ } ->
      f target;
      f value
  | For { iterable; clauses; body; _ } ->
      f iterable;
      List.iter (loop_clause f) clauses;
      block body
  | While { condition; clauses; body } ->
      f condition;
      List.iter (loop_clause f) clauses;
      block body
  | Parallel body | Proof body -> block body
  | Statement_error -> ()

let rec statement f written = statement_parts ~expression:f ~statement:(statement f) written
let block f (block : block) = List.iter (statement f) block.statements
let children f value = expression_parts ~expression:f ~statement:(statement f) value

let generic_parameter f (parameter : generic_parameter) =
  match parameter.kind with
  | Type_parameter (_, bounds) -> List.iter (path_type f) bounds
  | Value_parameter (_, type_) -> type_expression f type_
  | Capability_parameter _ | Generic_error -> ()

let type_head f (head : type_head) = List.iter (generic_parameter f) head.generics
let definition_name f = function Plain_name _ -> () | Member_name (head, _) -> type_head f head

let parameter f (parameter : parameter) =
  match parameter.kind with
  | Named_parameter { type_; default; _ } ->
      type_expression f type_;
      Option.iter f default
  | Self_parameter _ | Parameter_error -> ()

let signature f (signature : signature) =
  definition_name f signature.name;
  List.iter (generic_parameter f) signature.generics;
  List.iter (parameter f) signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Yields (_, type_) | Lends (_, type_)) -> type_expression f type_
  | None -> ());
  List.iter (clause f) signature.clauses

let function_definition f (definition : function_definition) =
  signature f definition.signature;
  block f definition.body

let field f (field : field) =
  match field.kind with
  | Field_declaration { type_; default; _ } ->
      type_expression f type_;
      Option.iter f default
  | Field_error -> ()

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
        (fun (member : trait_member line) ->
          match member.kind with
          | Trait_method { signature = method_; body } ->
              signature f method_;
              Option.iter (block f) body
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
        (fun (member : impl_member line) ->
          match member.kind with
          | Impl_method function_ -> function_definition f function_
          | Associated_definition (_, type_) -> type_expression f type_
          | Impl_member_error -> ())
        members
  | Capability { members; _ } ->
      List.iter
        (fun (member : capability_member line) ->
          match member.kind with
          | Capability_method method_ -> signature f method_
          | Capability_member_error -> ())
        members
  | Constant { name; type_; value } ->
      definition_name f name;
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
  | Definition_error _ -> ()

(* Visits every name in a definition, references and the names that bind,
   in expressions, patterns, types, clauses, and heads. *)
let walk_names ~on_name:add (definition_ : definition) =
  let path (written : path) =
    List.iter add written.modules;
    add written.last
  in
  let rec type_ (written : type_expression) =
    match written.kind with
    | Path_type written -> path_type_ written
    | Any_type written -> path_type_ written
    | Self_type key -> Option.iter add key
    | Associated (base, key) ->
        add base;
        add key
    | Function_type { inputs; output; clauses } ->
        List.iter (fun (_, input) -> type_ input) inputs;
        Option.iter type_ output;
        List.iter clause_ clauses
    | Type_error -> ()
  and path_type_ (written : path_type) =
    path written.path;
    List.iter
      (function
        | Type_argument argument -> type_ argument
        | Count _ -> ()
        | Count_name name -> add name
        | Constraint (name, argument) ->
            add name;
            type_ argument)
      written.arguments
  and clause_ (written : clause) =
    match written.kind with
    | Uses capabilities -> List.iter path_type_ capabilities
    | Requires value | Ensures value -> expression value
    | Decreases measures -> List.iter expression measures
    | Cost cost -> (
        (match cost.resource with
        | Calls (Call_parameter name) -> add name
        | Calls (Call_capability written) -> path_type_ written
        | Calls (Call_method (written, name)) ->
            path_type_ written;
            add name
        | Time | Allocations | Allocated_bytes -> ());
        match cost.bound with
        | Big_o value | At_most value | Exactly value -> expression value
        | Finite -> ())
    | Clause_error -> ()
  and literal_string (literal : string_literal) =
    Option.iter path literal.tag;
    List.iter (fun (value, _) -> expression value) literal.rest
  and expression (value : expression) =
    match value.kind with
    | Name written -> path written
    | Member (base, name) ->
        expression base;
        add name
    | String literal -> literal_string literal
    | Call (callee, arguments) ->
        expression callee;
        List.iter
          (fun (argument : argument) ->
            Option.iter add argument.label;
            expression argument.value)
          arguments
    | With (base, updates) ->
        expression base;
        List.iter
          (fun (update : update) ->
            match update.kind with
            | Update { field; path = rest; value } ->
                add field;
                List.iter add rest;
                Option.iter expression value
            | Update_error -> ())
          updates
    | Is { value = tested; pattern = written; _ } ->
        expression tested;
        pattern written
    | Quantified { binder; body; _ } ->
        (match binder with
        | Binder_in (written, collection) ->
            pattern written;
            expression collection
        | Binder_type (name, written) ->
            add name;
            type_ written);
        expression body
    | Lambda { parameters; body } ->
        List.iter pattern parameters;
        block_ body
    | Match { scrutinees; arms } ->
        List.iter expression scrutinees;
        List.iter
          (fun (arm : arm) ->
            List.iter pattern arm.patterns;
            Option.iter expression arm.guard;
            statement_ arm.body)
          arms
    | Bracket (base, items) ->
        expression base;
        List.iter
          (function
            | Item item -> expression item
            | Item_constraint (name, written) ->
                add name;
                type_ written)
          items
    | _ -> expression_parts ~expression ~statement:statement_ value
  and statement_ (written : statement) =
    match written.kind with
    | Let { pattern = bound; annotation; value; else_; _ } ->
        Option.iter type_ annotation;
        expression value;
        Option.iter block_ else_;
        pattern bound
    | For { pattern = bound; iterable; clauses; body; _ } ->
        expression iterable;
        pattern bound;
        List.iter (loop_clause expression) clauses;
        block_ body
    | _ -> statement_parts ~expression ~statement:statement_ written
  and block_ (written : block) = List.iter statement_ written.statements
  and pattern (written : pattern) =
    match written.kind with
    | Wildcard | Pattern_error -> ()
    | Binding_or_constant name -> add name
    | Qualified_constant constant -> constant_ constant
    | Literal literal -> literal_ literal
    | Pattern_range { start; stop; _ } ->
        range_end start;
        range_end stop
    | Variant { name; fields } ->
        path name;
        Option.iter (List.iter field_pattern) fields
    | Record fields -> List.iter field_pattern fields
    | Alternatives alternatives -> List.iter pattern alternatives
  and field_pattern (written : pattern_field) =
    match written.kind with
    | Named_field (name, inner) ->
        add name;
        pattern inner
    | Field inner -> pattern inner
    | Rest -> ()
  and literal_ = function
    | Literal_string literal -> literal_string literal
    | Literal_integer _ | Literal_true | Literal_false -> ()
  and constant_ = function
    | Module_constant written -> path written
    | Type_constant (written, name) ->
        path written;
        add name
  and range_end (written : range_end) =
    match written.kind with
    | End_literal literal -> literal_ literal
    | End_constant constant -> constant_ constant
    | End_name name -> add name
  in
  let generic (written : generic_parameter) =
    match written.kind with
    | Type_parameter (name, bounds) ->
        add name;
        List.iter path_type_ bounds
    | Value_parameter (name, written) ->
        add name;
        type_ written
    | Capability_parameter name -> add name
    | Generic_error -> ()
  in
  let head (written : type_head) =
    path written.path;
    List.iter generic written.generics
  in
  let definition_name = function
    | Plain_name name -> add name
    | Member_name (written, name) ->
        head written;
        add name
  in
  let parameter_ (written : parameter) =
    match written.kind with
    | Named_parameter { name; type_ = written; default; _ } ->
        add name;
        type_ written;
        Option.iter expression default
    | Self_parameter _ | Parameter_error -> ()
  in
  let signature_ (written : signature) =
    definition_name written.name;
    List.iter generic written.generics;
    List.iter parameter_ written.parameters;
    (match written.result with
    | Some (Returns result | Yields (_, result) | Lends (_, result)) -> type_ result
    | None -> ());
    List.iter clause_ written.clauses
  in
  let fields (written : field list) =
    List.iter
      (fun (field : field) ->
        match field.kind with
        | Field_declaration { name; type_ = written; default } ->
            add name;
            type_ written;
            Option.iter expression default
        | Field_error -> ())
      written
  in
  match definition_.kind with
  | Function { signature = written; body } ->
      signature_ written;
      block_ body
  | Type_definition { name; generics; body; clauses } ->
      add name;
      List.iter generic generics;
      (match body with
      | Fields written -> fields written
      | Variants variants ->
          List.iter
            (fun (variant : variant) ->
              add variant.name;
              Option.iter fields variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> expression value
          | Derives traits -> List.iter path_type_ traits)
        clauses
  | Trait { name; generics; requires; members } ->
      add name;
      List.iter generic generics;
      List.iter path_type_ requires;
      List.iter
        (fun (member : trait_member line) ->
          match member.kind with
          | Trait_method { signature = written; body } ->
              signature_ written;
              Option.iter block_ body
          | Associated_type (name, bounds) ->
              add name;
              List.iter path_type_ bounds
          | Law law ->
              add law.name;
              List.iter parameter_ law.parameters;
              List.iter expression law.requires;
              block_ law.body
          | Trait_member_error -> ())
        members
  | Impl { trait_; type_ = written; uses; members } ->
      path_type_ trait_;
      head written;
      List.iter path_type_ uses;
      List.iter
        (fun (member : impl_member line) ->
          match member.kind with
          | Impl_method { signature = method_; body } ->
              signature_ method_;
              block_ body
          | Associated_definition (name, written) ->
              add name;
              type_ written
          | Impl_member_error -> ())
        members
  | Capability { name; members } ->
      add name;
      List.iter
        (fun (member : capability_member line) ->
          match member.kind with
          | Capability_method written -> signature_ written
          | Capability_member_error -> ())
        members
  | Constant { name; type_ = written; value } ->
      definition_name name;
      type_ written;
      expression value
  | Test { name; uses; body } ->
      literal_string name;
      List.iter path_type_ uses;
      block_ body
  | Theorem { name; generics; parameters; clauses; body } ->
      add name;
      List.iter generic generics;
      List.iter parameter_ parameters;
      List.iter clause_ clauses;
      block_ body
  | Law_proof { trait_; law; type_ = written; body } ->
      path_type_ trait_;
      add law;
      type_ written;
      block_ body
  | Definition_error { name; _ } -> Option.iter definition_name name

(* Every name in a definition, in source order. Tools use it to find the
   name at a position, and checks to find every binding. *)
let names definition_ =
  let found = ref [] in
  walk_names ~on_name:(fun name -> found := name :: !found) definition_;
  List.stable_sort
    (fun (left : name) (right : name) -> compare left.span.start right.span.start)
    !found

let rec visit_type_expression on_expression (type_ : Syntax.type_expression) =
  match type_.kind with
  | Path_type path -> visit_path_type on_expression path
  | Function_type { inputs; output; clauses; _ } ->
      List.iter
        (fun (input : Syntax.function_input) -> visit_type_expression on_expression input.type_)
        inputs;
      Option.iter (visit_type_expression on_expression) output;
      List.iter (visit_clause on_expression) clauses
  | View_type viewed -> visit_type_expression on_expression viewed
  | Self_type _ | Associated _ | Type_error -> ()

and visit_path_type on_expression (path : Syntax.path_type) =
  List.iter (visit_type_argument on_expression) path.arguments

and visit_type_argument on_expression = function
  | Type_argument type_ | Constraint (_, type_) -> visit_type_expression on_expression type_
  | Count _ | Count_name _ -> ()

and visit_capability_reference on_expression (reference : Syntax.capability_reference) =
  match reference.kind with
  | Capability_path path -> visit_path_type on_expression path
  | Self_capabilities _ | Associated_capabilities _ | Generic_capability _ -> ()

and visit_condition on_expression (condition : Syntax.condition) =
  List.iter
    (fun (bound : Syntax.bound_condition) ->
      visit_type_expression on_expression bound.subject;
      List.iter (visit_path_type on_expression) bound.bounds)
    condition

and visit_capability_use on_expression (use : Syntax.capability_use) =
  visit_capability_reference on_expression use.capability;
  Option.iter (visit_condition on_expression) use.unless;
  List.iter on_expression use.unless_values

and visit_clause on_expression (clause : Syntax.clause) =
  Option.iter (visit_condition on_expression) clause.condition;
  match clause.kind with
  | Uses uses -> List.iter (visit_capability_use on_expression) uses
  | Requires value | Ensures value -> on_expression value
  | Decreases measures -> List.iter on_expression measures
  | Modifies parts -> List.iter on_expression parts
  | Cost cost -> (
      match cost.bound with Big_o value | At_most value | Exactly value -> on_expression value)
  | Clause_error -> ()

and visit_loop_clause on_expression (clause : Syntax.loop_clause) =
  Option.iter (visit_condition on_expression) clause.condition;
  match clause.kind with
  | Invariant value -> on_expression value
  | Loop_decreases measures -> List.iter on_expression measures
  | Loop_cost cost -> (
      match cost.bound with Big_o value | At_most value | Exactly value -> on_expression value)

and visit_string_literal on_expression (literal : Syntax.string_literal) =
  List.iter (fun (value, _) -> on_expression value) literal.rest

let visit_expression_parts ~on_expression ~on_statement (value : Syntax.expression) =
  let visit_block (block : Syntax.block) = List.iter on_statement block.statements in
  match value.kind with
  | Integer _ | Float _ | True | False | Todo | Unreachable | Break | Continue | Self_value
  | Self_type_value | Name _ | Expression_error ->
      ()
  | String literal -> visit_string_literal on_expression literal
  | Member (inner, _)
  | Try inner
  | Prefix (_, inner)
  | Mode (_, inner)
  | Echo inner
  | Parenthesized inner ->
      on_expression inner
  | Is { value = inner; _ } -> on_expression inner
  | Bracket (inner, items) ->
      on_expression inner;
      List.iter
        (function
          | Syntax.Item item -> on_expression item
          | Item_constraint (_, type_) -> visit_type_expression on_expression type_)
        items
  | Call (callee, arguments) ->
      on_expression callee;
      List.iter (fun (argument : Syntax.argument) -> on_expression argument.value) arguments
  | With (base, updates) ->
      on_expression base;
      List.iter
        (fun (update : Syntax.update) ->
          match update.kind with Update { value; _ } -> on_expression value | Update_error -> ())
        updates
  | Binary { left; right; _ } ->
      on_expression left;
      on_expression right
  | Range { start; stop; _ } ->
      Option.iter on_expression start;
      Option.iter on_expression stop
  | Quantified { binder; body; _ } ->
      (match binder with
      | Binder_in (_, collection) -> on_expression collection
      | Binder_type (_, type_) -> visit_type_expression on_expression type_);
      on_expression body
  | Return value -> Option.iter on_expression value
  | List items -> List.iter on_expression items
  | Map entries ->
      List.iter
        (fun (key, value) ->
          on_expression key;
          on_expression value)
        entries
  | Lambda { body; _ } -> visit_block body
  | If { condition; then_; else_ } -> (
      on_expression condition;
      visit_block then_;
      match else_ with
      | Some (Else body) -> visit_block body
      | Some (Else_if value) -> on_expression value
      | None -> ())
  | Match { scrutinees; arms } ->
      List.iter on_expression scrutinees;
      List.iter
        (fun (arm : Syntax.arm) ->
          Option.iter on_expression arm.guard;
          on_statement arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter on_expression implementations;
      visit_block body
  | Block body -> visit_block body

let visit_statement_parts ~on_expression ~on_statement (parent : Syntax.statement) =
  let visit_block (block : Syntax.block) = List.iter on_statement block.statements in
  match parent.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (visit_type_expression on_expression) annotation;
      on_expression value;
      Option.iter visit_block else_
  | Expression value | Assert { value; _ } -> on_expression value
  | Assignment { target; value; _ } ->
      on_expression target;
      on_expression value
  | For { annotation; iterable; clauses; body; _ } ->
      Option.iter (visit_type_expression on_expression) annotation;
      on_expression iterable;
      List.iter (visit_loop_clause on_expression) clauses;
      visit_block body
  | While { condition; clauses; body } ->
      on_expression condition;
      List.iter (visit_loop_clause on_expression) clauses;
      visit_block body
  | Parallel body | Concurrent body | Proof body -> visit_block body
  | Statement_error -> ()

let rec visit_statement on_expression (parent : Syntax.statement) =
  visit_statement_parts ~on_expression ~on_statement:(visit_statement on_expression) parent

let visit_block on_expression (block : Syntax.block) =
  List.iter (visit_statement on_expression) block.statements

let visit_children on_expression value =
  visit_expression_parts ~on_expression ~on_statement:(visit_statement on_expression) value

let contains_break (body : Syntax.block) =
  let has_break = ref false in
  let rec search_statement (statement : Syntax.statement) =
    match statement.kind with
    | For _ | While _ -> ()
    | _ ->
        visit_statement_parts ~on_expression:search_expression ~on_statement:search_statement
          statement
  and search_expression (value : Syntax.expression) =
    match value.kind with
    | Break -> has_break := true
    | Lambda _ -> ()
    | _ ->
        visit_expression_parts ~on_expression:search_expression ~on_statement:search_statement value
  in
  List.iter search_statement body.statements;
  !has_break

let visit_generic_parameter on_expression (parameter : Syntax.generic_parameter) =
  match parameter.kind with
  | Type_parameter (_, bounds) -> List.iter (visit_path_type on_expression) bounds
  | Value_parameter (_, type_) -> visit_type_expression on_expression type_
  | Generic_error -> ()

let visit_type_head on_expression (head : Syntax.type_head) =
  List.iter (visit_generic_parameter on_expression) head.generics

let visit_definition_name on_expression = function
  | Syntax.Plain_name _ -> ()
  | Member_name (head, _) -> visit_type_head on_expression head

let visit_parameter on_expression (parameter : Syntax.parameter) =
  match parameter.kind with
  | Named_parameter { type_; default; _ } ->
      visit_type_expression on_expression type_;
      Option.iter on_expression default
  | Self_parameter _ | Parameter_error -> ()

let visit_signature on_expression (signature : Syntax.signature) =
  visit_definition_name on_expression signature.name;
  List.iter (visit_generic_parameter on_expression) signature.generics;
  List.iter (visit_parameter on_expression) signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Lends (_, type_)) -> visit_type_expression on_expression type_
  | None -> ());
  List.iter (visit_clause on_expression) signature.clauses

let visit_function_definition ?on_statement:visit on_expression
    (definition : Syntax.function_definition) =
  visit_signature on_expression definition.signature;
  match visit with
  | Some visit -> List.iter visit definition.body.statements
  | None -> visit_block on_expression definition.body

let visit_field on_expression (field : Syntax.field) =
  match field.kind with
  | Field_declaration { type_; default; _ } ->
      visit_type_expression on_expression type_;
      Option.iter on_expression default
  | Field_error -> ()

let visit_definition ?on_statement:visit on_expression (definition : Syntax.definition) =
  let walk_block (body : Syntax.block) =
    match visit with
    | Some visit -> List.iter visit body.statements
    | None -> visit_block on_expression body
  in
  match definition.kind with
  | Function function_ -> visit_function_definition ?on_statement:visit on_expression function_
  | Method_declaration declared -> visit_signature on_expression declared
  | Type_definition { generics; body; clauses; _ } ->
      List.iter (visit_generic_parameter on_expression) generics;
      (match body with
      | Fields fields -> List.iter (visit_field on_expression) fields
      | Variants variants ->
          List.iter
            (fun (variant : Syntax.variant) ->
              Option.iter (List.iter (visit_field on_expression)) variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : Syntax.type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> on_expression value
          | Derives traits -> List.iter (visit_path_type on_expression) traits)
        clauses
  | Trait { generics; requires; members; _ } ->
      List.iter (visit_generic_parameter on_expression) generics;
      List.iter (visit_path_type on_expression) requires;
      List.iter
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with
          | Associated_type (_, bounds) -> List.iter (visit_path_type on_expression) bounds
          | Law law ->
              List.iter (visit_parameter on_expression) law.parameters;
              List.iter on_expression law.requires;
              walk_block law.body
          | Associated_capability _ | Trait_member_error -> ())
        members
  | Impl { trait_; type_; uses; members } ->
      visit_path_type on_expression trait_;
      visit_type_head on_expression type_;
      List.iter (visit_capability_reference on_expression) uses;
      List.iter
        (fun (member : Syntax.impl_member Syntax.node) ->
          match member.kind with
          | Associated_definition (_, type_) -> visit_type_expression on_expression type_
          | Capability_definition (_, capabilities) ->
              List.iter (visit_capability_use on_expression) capabilities
          | Impl_member_error -> ())
        members
  | Capability _ -> ()
  | Constant { name; type_; value } ->
      visit_definition_name on_expression name;
      visit_type_expression on_expression type_;
      on_expression value
  | Test { uses; body; _ } ->
      List.iter (visit_capability_reference on_expression) uses;
      walk_block body
  | Theorem { generics; parameters; clauses; body; _ } ->
      List.iter (visit_generic_parameter on_expression) generics;
      List.iter (visit_parameter on_expression) parameters;
      List.iter (visit_clause on_expression) clauses;
      walk_block body
  | Law_proof { trait_; type_; body; _ } ->
      visit_path_type on_expression trait_;
      visit_type_head on_expression type_;
      walk_block body
  | Definition_error _ -> ()

let walk_names ~on_name (definition : Syntax.definition) =
  let walk_path (path : Syntax.path) =
    List.iter on_name path.modules;
    on_name path.last
  in
  let rec walk_type (type_ : Syntax.type_expression) =
    match type_.kind with
    | Path_type path -> walk_path_type path
    | Self_type key -> Option.iter on_name key
    | Associated (base, key) ->
        on_name base;
        on_name key
    | Function_type { inputs; output; clauses; _ } ->
        List.iter
          (fun (input : Syntax.function_input) ->
            Option.iter on_name input.name;
            walk_type input.type_)
          inputs;
        Option.iter walk_type output;
        List.iter walk_clause clauses
    | View_type viewed -> walk_type viewed
    | Type_error -> ()
  and walk_path_type (path_type : Syntax.path_type) =
    walk_path path_type.path;
    List.iter
      (function
        | Syntax.Type_argument argument -> walk_type argument
        | Count _ -> ()
        | Count_name name -> on_name name
        | Constraint (name, argument) ->
            on_name name;
            walk_type argument)
      path_type.arguments
  and walk_capability (reference : Syntax.capability_reference) =
    match reference.kind with
    | Capability_path path -> walk_path_type path
    | Self_capabilities name | Generic_capability name -> on_name name
    | Associated_capabilities (base, name) ->
        on_name base;
        on_name name
  and walk_condition (condition : Syntax.condition) =
    List.iter
      (fun (bound : Syntax.bound_condition) ->
        walk_type bound.subject;
        List.iter walk_path_type bound.bounds)
      condition
  and walk_capability_use (use : Syntax.capability_use) =
    walk_capability use.capability;
    Option.iter walk_condition use.unless;
    List.iter walk_expression use.unless_values
  and walk_loop_clause (clause : Syntax.loop_clause) =
    Option.iter walk_condition clause.condition;
    visit_loop_clause walk_expression { clause with condition = None }
  and walk_clause (clause : Syntax.clause) =
    Option.iter walk_condition clause.condition;
    match clause.kind with
    | Uses uses -> List.iter walk_capability_use uses
    | Requires value | Ensures value -> walk_expression value
    | Decreases measures -> List.iter walk_expression measures
    | Modifies parts -> List.iter walk_expression parts
    | Cost cost -> (
        (match cost.resource with
        | Calls (Call_parameter name) -> on_name name
        | Calls (Call_capability capability) -> walk_path_type capability
        | Calls (Call_method (capability, name)) ->
            walk_path_type capability;
            on_name name
        | Metric _ -> ());
        match cost.bound with Big_o value | At_most value | Exactly value -> walk_expression value)
    | Clause_error -> ()
  and walk_string_literal (literal : Syntax.string_literal) =
    Option.iter walk_path literal.tag;
    List.iter (fun (value, _) -> walk_expression value) literal.rest
  and walk_expression (value : Syntax.expression) =
    match value.kind with
    | Name name -> on_name name
    | Member (base, name) ->
        walk_expression base;
        on_name name
    | String literal -> walk_string_literal literal
    | Call (callee, arguments) ->
        walk_expression callee;
        List.iter
          (fun (argument : Syntax.argument) ->
            Option.iter on_name argument.label;
            walk_expression argument.value)
          arguments
    | With (base, updates) ->
        walk_expression base;
        List.iter
          (fun (update : Syntax.update) ->
            match update.kind with
            | Update { path; value } ->
                List.iter on_name path;
                walk_expression value
            | Update_error -> ())
          updates
    | Is { value = tested; pattern; _ } ->
        walk_expression tested;
        walk_pattern pattern
    | Quantified { binder; body; _ } ->
        (match binder with
        | Binder_in (bound, collection) ->
            walk_pattern bound;
            walk_expression collection
        | Binder_type (name, type_) ->
            on_name name;
            walk_type type_);
        walk_expression body
    | Lambda { parameters; body } ->
        List.iter walk_pattern parameters;
        walk_block body
    | Match { scrutinees; arms } ->
        List.iter walk_expression scrutinees;
        List.iter
          (fun (arm : Syntax.arm) ->
            List.iter walk_pattern arm.patterns;
            Option.iter walk_expression arm.guard;
            walk_statement arm.body)
          arms
    | Bracket (base, items) ->
        walk_expression base;
        List.iter
          (function
            | Syntax.Item item -> walk_expression item
            | Item_constraint (name, type_) ->
                on_name name;
                walk_type type_)
          items
    | _ -> visit_expression_parts ~on_expression:walk_expression ~on_statement:walk_statement value
  and walk_statement (statement : Syntax.statement) =
    match statement.kind with
    | Let { pattern = bound; annotation; value; else_; _ } ->
        Option.iter walk_type annotation;
        walk_expression value;
        Option.iter walk_block else_;
        walk_pattern bound
    | For { pattern = bound; annotation; iterable; clauses; body; _ } ->
        Option.iter walk_type annotation;
        walk_expression iterable;
        walk_pattern bound;
        List.iter walk_loop_clause clauses;
        walk_block body
    | While { condition; clauses; body } ->
        walk_expression condition;
        List.iter walk_loop_clause clauses;
        walk_block body
    | _ ->
        visit_statement_parts ~on_expression:walk_expression ~on_statement:walk_statement statement
  and walk_block (block : Syntax.block) = List.iter walk_statement block.statements
  and walk_pattern (pattern : Syntax.pattern) =
    match pattern.kind with
    | Wildcard | Pattern_error -> ()
    | Binding name -> on_name name
    | Qualified_constant constant -> walk_constant constant
    | Literal literal -> walk_literal literal
    | Pattern_range { start; stop; _ } ->
        walk_range_end start;
        walk_range_end stop
    | Variant { name; fields } ->
        on_name name;
        Option.iter (List.iter walk_pattern_field) fields
    | Record fields -> List.iter walk_pattern_field fields
    | Tuple patterns | Alternatives patterns -> List.iter walk_pattern patterns
  and walk_pattern_field (field : Syntax.pattern_field) =
    match field.kind with
    | Named_field (name, inner) ->
        on_name name;
        walk_pattern inner
    | Field inner -> walk_pattern inner
    | Rest -> ()
  and walk_literal = function
    | Literal_string literal -> walk_string_literal literal
    | Literal_integer _ | Literal_true | Literal_false -> ()
  and walk_constant = function
    | Module_constant path -> walk_path path
    | Type_constant (path, name) ->
        walk_path path;
        on_name name
  and walk_range_end (range_end : Syntax.range_end) =
    match range_end.kind with
    | End_literal literal -> walk_literal literal
    | End_constant constant -> walk_constant constant
  in
  let walk_generic (parameter : Syntax.generic_parameter) =
    match parameter.kind with
    | Type_parameter (name, bounds) ->
        on_name name;
        List.iter walk_path_type bounds
    | Value_parameter (name, type_) ->
        on_name name;
        walk_type type_
    | Generic_error -> ()
  in
  let walk_head (head : Syntax.type_head) =
    walk_path head.path;
    List.iter walk_generic head.generics
  in
  let walk_definition_name = function
    | Syntax.Plain_name name -> on_name name
    | Member_name (head, name) ->
        walk_head head;
        on_name name
  in
  let walk_parameter (parameter : Syntax.parameter) =
    match parameter.kind with
    | Named_parameter { name; type_; default; _ } ->
        on_name name;
        walk_type type_;
        Option.iter walk_expression default
    | Self_parameter _ | Parameter_error -> ()
  in
  let walk_signature (signature : Syntax.signature) =
    walk_definition_name signature.name;
    List.iter walk_generic signature.generics;
    List.iter walk_parameter signature.parameters;
    (match signature.result with
    | Some (Returns result | Lends (_, result)) -> walk_type result
    | None -> ());
    List.iter walk_clause signature.clauses
  in
  let walk_fields (fields : Syntax.field list) =
    List.iter
      (fun (field : Syntax.field) ->
        match field.kind with
        | Field_declaration { name; type_; default } ->
            on_name name;
            walk_type type_;
            Option.iter walk_expression default
        | Field_error -> ())
      fields
  in
  match definition.kind with
  | Function { signature; body } ->
      walk_signature signature;
      walk_block body
  | Method_declaration signature -> walk_signature signature
  | Type_definition { name; generics; body; clauses; _ } ->
      on_name name;
      List.iter walk_generic generics;
      (match body with
      | Fields fields -> walk_fields fields
      | Variants variants ->
          List.iter
            (fun (variant : Syntax.variant) ->
              on_name variant.name;
              Option.iter walk_fields variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : Syntax.type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> walk_expression value
          | Derives traits -> List.iter walk_path_type traits)
        clauses
  | Trait { name; generics; requires; members } ->
      on_name name;
      List.iter walk_generic generics;
      List.iter walk_path_type requires;
      List.iter
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with
          | Associated_type (name, bounds) ->
              on_name name;
              List.iter walk_path_type bounds
          | Associated_capability name -> on_name name
          | Law law ->
              on_name law.name;
              List.iter walk_parameter law.parameters;
              List.iter walk_expression law.requires;
              walk_block law.body
          | Trait_member_error -> ())
        members
  | Impl { trait_; type_ = head; uses; members } ->
      walk_path_type trait_;
      walk_head head;
      List.iter walk_capability uses;
      List.iter
        (fun (member : Syntax.impl_member Syntax.node) ->
          match member.kind with
          | Associated_definition (name, type_) ->
              on_name name;
              walk_type type_
          | Capability_definition (name, capabilities) ->
              on_name name;
              List.iter walk_capability_use capabilities
          | Impl_member_error -> ())
        members
  | Capability { name; _ } -> on_name name
  | Constant { name; type_; value } ->
      walk_definition_name name;
      walk_type type_;
      walk_expression value
  | Test { name; uses; body } ->
      walk_string_literal name;
      List.iter walk_capability uses;
      walk_block body
  | Theorem { name; generics; parameters; clauses; body } ->
      on_name name;
      List.iter walk_generic generics;
      List.iter walk_parameter parameters;
      List.iter walk_clause clauses;
      walk_block body
  | Law_proof { trait_; law; type_ = head; body } ->
      walk_path_type trait_;
      on_name law;
      walk_head head;
      walk_block body
  | Definition_error { name; _ } -> Option.iter walk_definition_name name

let collect_names (spans : Source.Definition_span.t array) (definition : Syntax.definition) =
  let names = ref [] in
  walk_names ~on_name:(fun name -> names := name :: !names) definition;
  List.stable_sort
    (fun (left : Syntax.name) (right : Syntax.name) ->
      compare spans.(left.id).start spans.(right.id).start)
    !names

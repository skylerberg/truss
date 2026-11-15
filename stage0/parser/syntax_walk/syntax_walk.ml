open Syntax

let rec type_expression on_expression (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type on_expression path
  | Any_type path -> path_type on_expression path
  | Function_type { inputs; output; clauses; _ } ->
      List.iter (fun (input : function_input) -> type_expression on_expression input.type_) inputs;
      Option.iter (type_expression on_expression) output;
      List.iter (clause on_expression) clauses
  | Self_type _ | Associated _ | Type_error -> ()

and path_type on_expression (path : path_type) =
  List.iter (type_argument on_expression) path.arguments

and type_argument on_expression = function
  | Type_argument type_ | Constraint (_, type_) -> type_expression on_expression type_
  | Count _ | Count_name _ -> ()

and capability_reference on_expression (reference : capability_reference) =
  match reference.kind with
  | Capability_path path -> path_type on_expression path
  | Self_capabilities _ | Associated_capabilities _ -> ()

and clause on_expression (clause : clause) =
  match clause.kind with
  | Uses capabilities -> List.iter (capability_reference on_expression) capabilities
  | Requires value | Ensures value -> on_expression value
  | Decreases measures -> List.iter on_expression measures
  | Cost cost -> (
      match cost.bound with
      | Big_o value | At_most value | Exactly value -> on_expression value
      | Finite -> ())
  | Clause_error -> ()

and loop_clause on_expression (clause : loop_clause) =
  match clause.kind with
  | Invariant value -> on_expression value
  | Loop_decreases measures -> List.iter on_expression measures
  | Loop_cost cost -> (
      match cost.bound with
      | Big_o value | At_most value | Exactly value -> on_expression value
      | Finite -> ())

and string_literal on_expression (literal : string_literal) =
  List.iter (fun (value, _) -> on_expression value) literal.rest

let expression_parts ~expression:on_expression ~statement:on_statement (value : expression) =
  let block (block : block) = List.iter on_statement block.statements in
  match value.kind with
  | Integer _ | Float _ | True | False | Todo | Unreachable | Break | Continue | Self_value
  | Self_type_value | Name _ | Expression_error ->
      ()
  | String literal -> string_literal on_expression literal
  | Member (inner, _)
  | Try inner
  | Prefix (_, inner)
  | Mode (_, inner)
  | Any inner
  | Echo inner
  | Parenthesized inner ->
      on_expression inner
  | Is { value = inner; _ } -> on_expression inner
  | Bracket (inner, items) ->
      on_expression inner;
      List.iter
        (function
          | Item item -> on_expression item
          | Item_constraint (_, type_) -> type_expression on_expression type_)
        items
  | Call (callee, arguments) ->
      on_expression callee;
      List.iter (fun (argument : argument) -> on_expression argument.value) arguments
  | With (base, updates) ->
      on_expression base;
      List.iter
        (fun (update : update) ->
          match update.kind with
          | Update { value; _ } -> Option.iter on_expression value
          | Update_error -> ())
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
      | Binder_type (_, type_) -> type_expression on_expression type_);
      on_expression body
  | Return value -> Option.iter on_expression value
  | List items -> List.iter on_expression items
  | Map entries ->
      List.iter
        (fun (key, value) ->
          on_expression key;
          on_expression value)
        entries
  | Lambda { body; _ } -> block body
  | If { condition; then_; else_ } -> (
      on_expression condition;
      block then_;
      match else_ with
      | Some (Else body) -> block body
      | Some (Else_if value) -> on_expression value
      | None -> ())
  | Match { scrutinees; arms } ->
      List.iter on_expression scrutinees;
      List.iter
        (fun (arm : arm) ->
          Option.iter on_expression arm.guard;
          on_statement arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter on_expression implementations;
      block body
  | Block body -> block body

let statement_parts ~expression:on_expression ~statement:on_statement (parent : statement) =
  let block (block : block) = List.iter on_statement block.statements in
  match parent.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (type_expression on_expression) annotation;
      on_expression value;
      Option.iter block else_
  | Expression value | Assert { value; _ } -> on_expression value
  | Assignment { target; value; _ } ->
      on_expression target;
      on_expression value
  | For { annotation; iterable; clauses; body; _ } ->
      Option.iter (type_expression on_expression) annotation;
      on_expression iterable;
      List.iter (loop_clause on_expression) clauses;
      block body
  | While { condition; clauses; body } ->
      on_expression condition;
      List.iter (loop_clause on_expression) clauses;
      block body
  | Parallel body | Concurrent body | Proof body -> block body
  | Statement_error -> ()

let rec statement on_expression (parent : statement) =
  statement_parts ~expression:on_expression ~statement:(statement on_expression) parent

let block on_expression (block : block) = List.iter (statement on_expression) block.statements

let children on_expression value =
  expression_parts ~expression:on_expression ~statement:(statement on_expression) value

let contains_break (body : block) =
  let has_break = ref false in
  let rec search_statement (statement : statement) =
    match statement.kind with
    | For _ | While _ -> ()
    | _ -> statement_parts ~expression:search_expression ~statement:search_statement statement
  and search_expression (value : expression) =
    match value.kind with
    | Break -> has_break := true
    | Lambda _ -> ()
    | _ -> expression_parts ~expression:search_expression ~statement:search_statement value
  in
  List.iter search_statement body.statements;
  !has_break

let generic_parameter on_expression (parameter : generic_parameter) =
  match parameter.kind with
  | Type_parameter (_, bounds) -> List.iter (path_type on_expression) bounds
  | Value_parameter (_, type_) -> type_expression on_expression type_
  | Capability_parameter _ | Generic_error -> ()

let type_head on_expression (head : type_head) =
  List.iter (generic_parameter on_expression) head.generics

let definition_name on_expression = function
  | Plain_name _ -> ()
  | Member_name (head, _) -> type_head on_expression head

let parameter on_expression (parameter : parameter) =
  match parameter.kind with
  | Named_parameter { type_; default; _ } ->
      type_expression on_expression type_;
      Option.iter on_expression default
  | Self_parameter _ | Parameter_error -> ()

let signature on_expression (signature : signature) =
  definition_name on_expression signature.name;
  List.iter (generic_parameter on_expression) signature.generics;
  List.iter (parameter on_expression) signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Lends (_, type_)) -> type_expression on_expression type_
  | None -> ());
  List.iter (clause on_expression) signature.clauses

let function_definition ?statement:visit on_expression (definition : function_definition) =
  signature on_expression definition.signature;
  match visit with
  | Some visit -> List.iter visit definition.body.statements
  | None -> block on_expression definition.body

let field on_expression (field : field) =
  match field.kind with
  | Field_declaration { type_; default; _ } ->
      type_expression on_expression type_;
      Option.iter on_expression default
  | Field_error -> ()

let definition ?statement:visit on_expression (definition : definition) =
  let walk_block (body : block) =
    match visit with
    | Some visit -> List.iter visit body.statements
    | None -> block on_expression body
  in
  match definition.kind with
  | Function function_ -> function_definition ?statement:visit on_expression function_
  | Method_declaration declared -> signature on_expression declared
  | Type_definition { generics; body; clauses; _ } ->
      List.iter (generic_parameter on_expression) generics;
      (match body with
      | Fields fields -> List.iter (field on_expression) fields
      | Variants variants ->
          List.iter
            (fun (variant : variant) ->
              Option.iter (List.iter (field on_expression)) variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> on_expression value
          | Derives traits -> List.iter (path_type on_expression) traits)
        clauses
  | Trait { generics; requires; members; _ } ->
      List.iter (generic_parameter on_expression) generics;
      List.iter (path_type on_expression) requires;
      List.iter
        (fun (member : trait_member node) ->
          match member.kind with
          | Associated_type (_, bounds) -> List.iter (path_type on_expression) bounds
          | Law law ->
              List.iter (parameter on_expression) law.parameters;
              List.iter on_expression law.requires;
              walk_block law.body
          | Associated_capability _ | Trait_member_error -> ())
        members
  | Impl { trait_; type_; uses; members } ->
      path_type on_expression trait_;
      type_head on_expression type_;
      List.iter (capability_reference on_expression) uses;
      List.iter
        (fun (member : impl_member node) ->
          match member.kind with
          | Associated_definition (_, type_) -> type_expression on_expression type_
          | Capability_definition (_, capabilities) ->
              List.iter (capability_reference on_expression) capabilities
          | Impl_member_error -> ())
        members
  | Capability _ -> ()
  | Constant { name; type_; value } ->
      definition_name on_expression name;
      type_expression on_expression type_;
      on_expression value
  | Test { uses; body; _ } ->
      List.iter (capability_reference on_expression) uses;
      walk_block body
  | Theorem { generics; parameters; clauses; body; _ } ->
      List.iter (generic_parameter on_expression) generics;
      List.iter (parameter on_expression) parameters;
      List.iter (clause on_expression) clauses;
      walk_block body
  | Law_proof { trait_; type_; body; _ } ->
      path_type on_expression trait_;
      type_head on_expression type_;
      walk_block body
  | Definition_error _ -> ()

let walk_names ?(on_path_type = ignore) ~on_name (definition : definition) =
  let walk_path (path : path) =
    List.iter on_name path.modules;
    on_name path.last
  in
  let rec walk_type (type_ : type_expression) =
    match type_.kind with
    | Path_type path | Any_type path -> walk_path_type path
    | Self_type key -> Option.iter on_name key
    | Associated (base, key) ->
        on_name base;
        on_name key
    | Function_type { inputs; output; clauses; _ } ->
        List.iter
          (fun (input : function_input) ->
            Option.iter on_name input.name;
            walk_type input.type_)
          inputs;
        Option.iter walk_type output;
        List.iter walk_clause clauses
    | Type_error -> ()
  and walk_path_type (path_type : path_type) =
    on_path_type path_type;
    walk_path path_type.path;
    List.iter
      (function
        | Type_argument argument -> walk_type argument
        | Count _ -> ()
        | Count_name name -> on_name name
        | Constraint (name, argument) ->
            on_name name;
            walk_type argument)
      path_type.arguments
  and walk_capability (reference : capability_reference) =
    match reference.kind with
    | Capability_path path -> walk_path_type path
    | Self_capabilities name -> on_name name
    | Associated_capabilities (base, name) ->
        on_name base;
        on_name name
  and walk_clause (clause : clause) =
    match clause.kind with
    | Uses capabilities -> List.iter walk_capability capabilities
    | Requires value | Ensures value -> walk_expression value
    | Decreases measures -> List.iter walk_expression measures
    | Cost cost -> (
        (match cost.resource with
        | Calls (Call_parameter name) -> on_name name
        | Calls (Call_capability capability) -> walk_path_type capability
        | Calls (Call_method (capability, name)) ->
            walk_path_type capability;
            on_name name
        | Time | Allocations | Allocated_bytes -> ());
        match cost.bound with
        | Big_o value | At_most value | Exactly value -> walk_expression value
        | Finite -> ())
    | Clause_error -> ()
  and walk_string_literal (literal : string_literal) =
    Option.iter walk_path literal.tag;
    List.iter (fun (value, _) -> walk_expression value) literal.rest
  and walk_expression (value : expression) =
    match value.kind with
    | Name path -> walk_path path
    | Member (base, name) ->
        walk_expression base;
        on_name name
    | String literal -> walk_string_literal literal
    | Call (callee, arguments) ->
        walk_expression callee;
        List.iter
          (fun (argument : argument) ->
            Option.iter on_name argument.label;
            walk_expression argument.value)
          arguments
    | With (base, updates) ->
        walk_expression base;
        List.iter
          (fun (update : update) ->
            match update.kind with
            | Update { field; path = rest; value } ->
                on_name field;
                List.iter on_name rest;
                Option.iter walk_expression value
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
          (fun (arm : arm) ->
            List.iter walk_pattern arm.patterns;
            Option.iter walk_expression arm.guard;
            walk_statement arm.body)
          arms
    | Bracket (base, items) ->
        walk_expression base;
        List.iter
          (function
            | Item item -> walk_expression item
            | Item_constraint (name, type_) ->
                on_name name;
                walk_type type_)
          items
    | _ -> expression_parts ~expression:walk_expression ~statement:walk_statement value
  and walk_statement (statement : statement) =
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
        List.iter (loop_clause walk_expression) clauses;
        walk_block body
    | _ -> statement_parts ~expression:walk_expression ~statement:walk_statement statement
  and walk_block (block : block) = List.iter walk_statement block.statements
  and walk_pattern (pattern : pattern) =
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
    | Alternatives alternatives -> List.iter walk_pattern alternatives
  and walk_pattern_field (field : pattern_field) =
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
  and walk_range_end (range_end : range_end) =
    match range_end.kind with
    | End_literal literal -> walk_literal literal
    | End_constant constant -> walk_constant constant
  in
  let walk_generic (parameter : generic_parameter) =
    match parameter.kind with
    | Type_parameter (name, bounds) ->
        on_name name;
        List.iter walk_path_type bounds
    | Value_parameter (name, type_) ->
        on_name name;
        walk_type type_
    | Capability_parameter name -> on_name name
    | Generic_error -> ()
  in
  let walk_head (head : type_head) =
    walk_path head.path;
    List.iter walk_generic head.generics
  in
  let walk_definition_name = function
    | Plain_name name -> on_name name
    | Member_name (head, name) ->
        walk_head head;
        on_name name
  in
  let walk_parameter (parameter : parameter) =
    match parameter.kind with
    | Named_parameter { name; type_; default; _ } ->
        on_name name;
        walk_type type_;
        Option.iter walk_expression default
    | Self_parameter _ | Parameter_error -> ()
  in
  let walk_signature (signature : signature) =
    walk_definition_name signature.name;
    List.iter walk_generic signature.generics;
    List.iter walk_parameter signature.parameters;
    (match signature.result with
    | Some (Returns result | Lends (_, result)) -> walk_type result
    | None -> ());
    List.iter walk_clause signature.clauses
  in
  let walk_fields (fields : field list) =
    List.iter
      (fun (field : field) ->
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
  | Type_definition { name; generics; body; clauses } ->
      on_name name;
      List.iter walk_generic generics;
      (match body with
      | Fields fields -> walk_fields fields
      | Variants variants ->
          List.iter
            (fun (variant : variant) ->
              on_name variant.name;
              Option.iter walk_fields variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> walk_expression value
          | Derives traits -> List.iter walk_path_type traits)
        clauses
  | Trait { name; generics; requires; members } ->
      on_name name;
      List.iter walk_generic generics;
      List.iter walk_path_type requires;
      List.iter
        (fun (member : trait_member node) ->
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
        (fun (member : impl_member node) ->
          match member.kind with
          | Associated_definition (name, type_) ->
              on_name name;
              walk_type type_
          | Capability_definition (name, capabilities) ->
              on_name name;
              List.iter walk_capability capabilities
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

let span_table (root : definition) : Source.Definition_span.t array =
  let spans = Array.make (root.id + 1) root.span in
  let rec record_pattern (pattern : pattern) =
    spans.(pattern.id) <- pattern.span;
    match pattern.kind with
    | Wildcard | Binding _ | Qualified_constant _ | Literal _ | Pattern_error -> ()
    | Pattern_range { start; stop; _ } ->
        spans.(start.id) <- start.span;
        spans.(stop.id) <- stop.span
    | Variant { fields; _ } -> Option.iter (List.iter record_pattern_field) fields
    | Record fields -> List.iter record_pattern_field fields
    | Alternatives alternatives -> List.iter record_pattern alternatives
  and record_pattern_field (field : pattern_field) =
    match field.kind with
    | Named_field (_, inner) | Field inner -> record_pattern inner
    | Rest -> ()
  in
  let rec record_expression (value : expression) =
    spans.(value.id) <- value.span;
    (match value.kind with
    | Is { pattern; _ } -> record_pattern pattern
    | With (_, updates) ->
        List.iter (fun (update : update) -> spans.(update.id) <- update.span) updates
    | Quantified { binder = Binder_in (bound, _); _ } -> record_pattern bound
    | Lambda { parameters; _ } -> List.iter record_pattern parameters
    | Match { arms; _ } ->
        List.iter
          (fun (arm : arm) ->
            spans.(arm.id) <- arm.span;
            List.iter record_pattern arm.patterns)
          arms
    | _ -> ());
    expression_parts ~expression:record_expression ~statement:record_statement value
  and record_statement (statement : statement) =
    spans.(statement.id) <- statement.span;
    (match statement.kind with
    | Let { pattern = bound; _ } -> record_pattern bound
    | For { pattern = bound; clauses; _ } ->
        record_pattern bound;
        List.iter (fun (clause : loop_clause) -> spans.(clause.id) <- clause.span) clauses
    | While { clauses; _ } ->
        List.iter (fun (clause : loop_clause) -> spans.(clause.id) <- clause.span) clauses
    | _ -> ());
    statement_parts ~expression:record_expression ~statement:record_statement statement
  in
  (match root.kind with
  | Function { signature = { clauses; _ }; _ }
  | Method_declaration { clauses; _ }
  | Theorem { clauses; _ } ->
      List.iter (fun (clause : clause) -> spans.(clause.id) <- clause.span) clauses
  | _ -> ());
  definition ~statement:record_statement record_expression root;
  walk_names
    ~on_path_type:(fun (path_type : path_type) -> spans.(path_type.id) <- path_type.span)
    ~on_name:ignore root;
  spans

let collect_names (definition : definition) =
  let names = ref [] in
  walk_names ~on_name:(fun name -> names := name :: !names) definition;
  List.stable_sort
    (fun (left : name) (right : name) -> compare left.span.start right.span.start)
    !names

let without_positions (definition : definition) : definition =
  let no_span = Source.Definition_span.zero_width 0 in
  let strip_name (name : name) = { name with span = no_span } in
  let strip_path (path : path) =
    { modules = List.map strip_name path.modules; last = strip_name path.last }
  in
  let rec strip_type (type_ : type_expression) : type_expression =
    {
      type_ with
      span = no_span;
      kind =
        (match type_.kind with
        | Path_type path -> Path_type (strip_path_type path)
        | Self_type name -> Self_type (Option.map strip_name name)
        | Associated (base, name) -> Associated (strip_name base, strip_name name)
        | Any_type path -> Any_type (strip_path_type path)
        | Function_type { inputs; output; clauses } ->
            Function_type
              {
                inputs =
                  List.map
                    (fun (input : function_input) ->
                      {
                        input with
                        name = Option.map strip_name input.name;
                        type_ = strip_type input.type_;
                      })
                    inputs;
                output = Option.map strip_type output;
                clauses = List.map strip_clause clauses;
              }
        | Type_error -> Type_error);
    }
  and strip_path_type (path_type : path_type) =
    {
      path_type with
      path = strip_path path_type.path;
      arguments = List.map strip_type_argument path_type.arguments;
      span = no_span;
    }
  and strip_type_argument = function
    | Type_argument type_ -> Type_argument (strip_type type_)
    | Count (value, _) -> Count (value, no_span)
    | Count_name name -> Count_name (strip_name name)
    | Constraint (name, type_) -> Constraint (strip_name name, strip_type type_)
  and strip_capability (reference : capability_reference) : capability_reference =
    {
      reference with
      span = no_span;
      kind =
        (match reference.kind with
        | Capability_path path -> Capability_path (strip_path_type path)
        | Self_capabilities name -> Self_capabilities (strip_name name)
        | Associated_capabilities (base, name) ->
            Associated_capabilities (strip_name base, strip_name name));
    }
  and strip_clause (clause : clause) : clause =
    {
      clause with
      span = no_span;
      kind =
        (match clause.kind with
        | Uses capabilities -> Uses (List.map strip_capability capabilities)
        | Requires value -> Requires (strip_expression value)
        | Ensures value -> Ensures (strip_expression value)
        | Decreases measures -> Decreases (List.map strip_expression measures)
        | Cost cost -> Cost (strip_cost cost)
        | Clause_error -> Clause_error);
    }
  and strip_cost (cost : cost) =
    {
      cost with
      resource =
        (match cost.resource with
        | Calls (Call_parameter name) -> Calls (Call_parameter (strip_name name))
        | Calls (Call_capability capability) -> Calls (Call_capability (strip_path_type capability))
        | Calls (Call_method (capability, name)) ->
            Calls (Call_method (strip_path_type capability, strip_name name))
        | (Time | Allocations | Allocated_bytes) as resource -> resource);
      bound =
        (match cost.bound with
        | Big_o value -> Big_o (strip_expression value)
        | At_most value -> At_most (strip_expression value)
        | Exactly value -> Exactly (strip_expression value)
        | Finite -> Finite);
    }
  and strip_string_literal (literal : string_literal) =
    {
      literal with
      tag = Option.map strip_path literal.tag;
      first = strip_text literal.first;
      rest = List.map (fun (value, rest) -> (strip_expression value, strip_text rest)) literal.rest;
      span = no_span;
    }
  and strip_text (text : text) = { text with span = no_span }
  and strip_expression (value : expression) : expression =
    {
      value with
      span = no_span;
      kind =
        (match value.kind with
        | ( Integer _ | Float _ | True | False | Todo | Unreachable | Break | Continue | Self_value
          | Self_type_value | Expression_error ) as kind ->
            kind
        | String literal -> String (strip_string_literal literal)
        | Name path -> Name (strip_path path)
        | Member (base, name) -> Member (strip_expression base, strip_name name)
        | Bracket (base, items) ->
            Bracket
              ( strip_expression base,
                List.map
                  (function
                    | Item item -> Item (strip_expression item)
                    | Item_constraint (name, type_) ->
                        Item_constraint (strip_name name, strip_type type_))
                  items )
        | Call (callee, arguments) ->
            Call
              ( strip_expression callee,
                List.map
                  (fun (argument : argument) ->
                    {
                      label = Option.map strip_name argument.label;
                      value = strip_expression argument.value;
                    })
                  arguments )
        | Try inner -> Try (strip_expression inner)
        | With (base, updates) -> With (strip_expression base, List.map strip_update updates)
        | Prefix (operator, inner) -> Prefix (operator, strip_expression inner)
        | Mode (mode, inner) -> Mode (mode, strip_expression inner)
        | Any inner -> Any (strip_expression inner)
        | Binary { operator; left; right; _ } ->
            Binary
              {
                operator;
                operator_span = no_span;
                left = strip_expression left;
                right = strip_expression right;
              }
        | Is { value = tested; pattern; _ } ->
            Is
              {
                value = strip_expression tested;
                operator_span = no_span;
                pattern = strip_pattern pattern;
              }
        | Range { start; stop; inclusive; _ } ->
            Range
              {
                start = Option.map strip_expression start;
                operator_span = no_span;
                stop = Option.map strip_expression stop;
                inclusive;
              }
        | Quantified { quantifier; binder; body } ->
            Quantified
              {
                quantifier;
                binder =
                  (match binder with
                  | Binder_in (bound, collection) ->
                      Binder_in (strip_pattern bound, strip_expression collection)
                  | Binder_type (name, type_) -> Binder_type (strip_name name, strip_type type_));
                body = strip_expression body;
              }
        | Echo inner -> Echo (strip_expression inner)
        | Return inner -> Return (Option.map strip_expression inner)
        | Parenthesized inner -> Parenthesized (strip_expression inner)
        | List items -> List (List.map strip_expression items)
        | Map pairs ->
            Map
              (List.map (fun (key, value) -> (strip_expression key, strip_expression value)) pairs)
        | Lambda { parameters; body } ->
            Lambda { parameters = List.map strip_pattern parameters; body = strip_block body }
        | If { condition; then_; else_ } ->
            If
              {
                condition = strip_expression condition;
                then_ = strip_block then_;
                else_ =
                  Option.map
                    (function
                      | Else block -> Else (strip_block block)
                      | Else_if branch -> Else_if (strip_expression branch))
                    else_;
              }
        | Match { scrutinees; arms } ->
            Match
              { scrutinees = List.map strip_expression scrutinees; arms = List.map strip_arm arms }
        | Provide { implementations; body } ->
            Provide
              {
                implementations = List.map strip_expression implementations;
                body = strip_block body;
              }
        | Block block -> Block (strip_block block));
    }
  and strip_update (update : update) : update =
    {
      update with
      span = no_span;
      kind =
        (match update.kind with
        | Update { field; path = rest; value } ->
            Update
              {
                field = strip_name field;
                path = List.map strip_name rest;
                value = Option.map strip_expression value;
              }
        | Update_error -> Update_error);
    }
  and strip_arm (arm : arm) =
    {
      arm with
      patterns = List.map strip_pattern arm.patterns;
      guard = Option.map strip_expression arm.guard;
      body = strip_statement arm.body;
      span = no_span;
    }
  and strip_block (block : block) =
    { block with statements = List.map strip_statement block.statements; span = no_span }
  and strip_statement (statement : statement) : statement =
    {
      statement with
      span = no_span;
      kind =
        (match statement.kind with
        | Let { is_var; pattern = bound; annotation; value; else_ } ->
            Let
              {
                is_var;
                pattern = strip_pattern bound;
                annotation = Option.map strip_type annotation;
                value = strip_expression value;
                else_ = Option.map strip_block else_;
              }
        | Expression value -> Expression (strip_expression value)
        | Assignment { target; operator; value } ->
            Assignment
              { target = strip_expression target; operator; value = strip_expression value }
        | For { mode; pattern = bound; annotation; iterable; clauses; body } ->
            For
              {
                mode;
                pattern = strip_pattern bound;
                annotation = Option.map strip_type annotation;
                iterable = strip_expression iterable;
                clauses = List.map strip_loop_clause clauses;
                body = strip_block body;
              }
        | While { condition; clauses; body } ->
            While
              {
                condition = strip_expression condition;
                clauses = List.map strip_loop_clause clauses;
                body = strip_block body;
              }
        | Parallel body -> Parallel (strip_block body)
        | Concurrent body -> Concurrent (strip_block body)
        | Proof body -> Proof (strip_block body)
        | Assert { value; by_bit_vector } ->
            Assert { value = strip_expression value; by_bit_vector }
        | Statement_error -> Statement_error);
    }
  and strip_loop_clause (clause : loop_clause) : loop_clause =
    {
      clause with
      span = no_span;
      kind =
        (match clause.kind with
        | Invariant value -> Invariant (strip_expression value)
        | Loop_decreases measures -> Loop_decreases (List.map strip_expression measures)
        | Loop_cost cost -> Loop_cost (strip_cost cost));
    }
  and strip_pattern (pattern : pattern) : pattern =
    {
      pattern with
      span = no_span;
      kind =
        (match pattern.kind with
        | (Wildcard | Pattern_error) as kind -> kind
        | Binding name -> Binding (strip_name name)
        | Qualified_constant constant -> Qualified_constant (strip_constant constant)
        | Literal literal -> Literal (strip_literal literal)
        | Pattern_range { start; stop; inclusive } ->
            Pattern_range { start = strip_range_end start; stop = strip_range_end stop; inclusive }
        | Variant { name; fields } ->
            Variant
              { name = strip_name name; fields = Option.map (List.map strip_pattern_field) fields }
        | Record fields -> Record (List.map strip_pattern_field fields)
        | Alternatives alternatives -> Alternatives (List.map strip_pattern alternatives));
    }
  and strip_constant = function
    | Module_constant path -> Module_constant (strip_path path)
    | Type_constant (path, name) -> Type_constant (strip_path path, strip_name name)
  and strip_literal = function
    | Literal_string literal -> Literal_string (strip_string_literal literal)
    | (Literal_integer _ | Literal_true | Literal_false) as literal -> literal
  and strip_range_end (range_end : range_end) : range_end =
    {
      range_end with
      span = no_span;
      kind =
        (match range_end.kind with
        | End_literal literal -> End_literal (strip_literal literal)
        | End_constant constant -> End_constant (strip_constant constant));
    }
  and strip_pattern_field (field : pattern_field) : pattern_field =
    {
      field with
      span = no_span;
      kind =
        (match field.kind with
        | Named_field (name, inner) -> Named_field (strip_name name, strip_pattern inner)
        | Field inner -> Field (strip_pattern inner)
        | Rest -> Rest);
    }
  in
  let strip_generic (parameter : generic_parameter) : generic_parameter =
    {
      parameter with
      span = no_span;
      kind =
        (match parameter.kind with
        | Type_parameter (name, bounds) ->
            Type_parameter (strip_name name, List.map strip_path_type bounds)
        | Value_parameter (name, type_) -> Value_parameter (strip_name name, strip_type type_)
        | Capability_parameter name -> Capability_parameter (strip_name name)
        | Generic_error -> Generic_error);
    }
  in
  let strip_head (head : type_head) =
    {
      head with
      path = strip_path head.path;
      generics = List.map strip_generic head.generics;
      span = no_span;
    }
  in
  let strip_definition_name = function
    | Plain_name name -> Plain_name (strip_name name)
    | Member_name (head, name) -> Member_name (strip_head head, strip_name name)
  in
  let strip_parameter (parameter : parameter) : parameter =
    {
      parameter with
      span = no_span;
      kind =
        (match parameter.kind with
        | Named_parameter { name; mode; type_; default } ->
            Named_parameter
              {
                name = strip_name name;
                mode;
                type_ = strip_type type_;
                default = Option.map strip_expression default;
              }
        | (Self_parameter _ | Parameter_error) as kind -> kind);
    }
  in
  let strip_signature (signature : signature) =
    {
      name = strip_definition_name signature.name;
      generics = List.map strip_generic signature.generics;
      parameters = List.map strip_parameter signature.parameters;
      result =
        Option.map
          (function
            | Returns result -> Returns (strip_type result)
            | Lends (mode, result) -> Lends (mode, strip_type result))
          signature.result;
      clauses = List.map strip_clause signature.clauses;
    }
  in
  let strip_field (field : field) : field =
    {
      field with
      span = no_span;
      kind =
        (match field.kind with
        | Field_declaration { name; type_; default } ->
            Field_declaration
              {
                name = strip_name name;
                type_ = strip_type type_;
                default = Option.map strip_expression default;
              }
        | Field_error -> Field_error);
    }
  in
  let strip_node (node : _ node) kind = { node with kind; span = no_span } in
  let kind : definition_kind =
    match definition.kind with
    | Function { signature; body } ->
        Function { signature = strip_signature signature; body = strip_block body }
    | Method_declaration signature -> Method_declaration (strip_signature signature)
    | Type_definition { name; generics; body; clauses } ->
        Type_definition
          {
            name = strip_name name;
            generics = List.map strip_generic generics;
            body =
              (match body with
              | Fields fields -> Fields (List.map strip_field fields)
              | Variants variants ->
                  Variants
                    (List.map
                       (fun (variant : variant) ->
                         {
                           variant with
                           name = strip_name variant.name;
                           fields = Option.map (List.map strip_field) variant.fields;
                           span = no_span;
                         })
                       variants)
              | Type_todo -> Type_todo);
            clauses =
              List.map
                (fun (clause : type_clause) : type_clause ->
                  {
                    clause with
                    span = no_span;
                    kind =
                      (match clause.kind with
                      | Type_invariant value -> Type_invariant (strip_expression value)
                      | Derives traits -> Derives (List.map strip_path_type traits)
                      | Potential value -> Potential (strip_expression value));
                  })
                clauses;
          }
    | Trait { name; generics; requires; members } ->
        Trait
          {
            name = strip_name name;
            generics = List.map strip_generic generics;
            requires = List.map strip_path_type requires;
            members =
              List.map
                (fun (member : trait_member node) ->
                  strip_node member
                    (match member.kind with
                    | Associated_type (name, bounds) ->
                        Associated_type (strip_name name, List.map strip_path_type bounds)
                    | Associated_capability name -> Associated_capability (strip_name name)
                    | Law law ->
                        Law
                          {
                            name = strip_name law.name;
                            parameters = List.map strip_parameter law.parameters;
                            requires = List.map strip_expression law.requires;
                            body = strip_block law.body;
                          }
                    | Trait_member_error -> Trait_member_error))
                members;
          }
    | Impl { trait_; type_ = head; uses; members } ->
        Impl
          {
            trait_ = strip_path_type trait_;
            type_ = strip_head head;
            uses = List.map strip_capability uses;
            members =
              List.map
                (fun (member : impl_member node) ->
                  strip_node member
                    (match member.kind with
                    | Associated_definition (name, type_) ->
                        Associated_definition (strip_name name, strip_type type_)
                    | Capability_definition (name, capabilities) ->
                        Capability_definition
                          (strip_name name, List.map strip_capability capabilities)
                    | Impl_member_error -> Impl_member_error))
                members;
          }
    | Capability { name; members } ->
        Capability
          {
            name = strip_name name;
            members =
              List.map
                (fun (member : capability_member node) -> strip_node member member.kind)
                members;
          }
    | Constant { name; type_; value } ->
        Constant
          {
            name = strip_definition_name name;
            type_ = strip_type type_;
            value = strip_expression value;
          }
    | Test { name; uses; body } ->
        Test
          {
            name = strip_string_literal name;
            uses = List.map strip_capability uses;
            body = strip_block body;
          }
    | Theorem { name; generics; parameters; clauses; body } ->
        Theorem
          {
            name = strip_name name;
            generics = List.map strip_generic generics;
            parameters = List.map strip_parameter parameters;
            clauses = List.map strip_clause clauses;
            body = strip_block body;
          }
    | Law_proof { trait_; law; type_ = head; body } ->
        Law_proof
          {
            trait_ = strip_path_type trait_;
            law = strip_name law;
            type_ = strip_head head;
            body = strip_block body;
          }
    | Definition_error { intended; name } ->
        Definition_error { intended; name = Option.map strip_definition_name name }
  in
  {
    definition with
    kind;
    span = no_span;
    recovered = List.map (fun _ -> no_span) definition.recovered;
  }

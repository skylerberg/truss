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

let expression_parts ~expression:on_expression ~statement (value : expression) =
  let block (block : block) = List.iter statement block.statements in
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
          statement arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter on_expression implementations;
      block body
  | Block body -> block body

let statement_parts ~expression:on_expression ~statement (written : statement) =
  let block (block : block) = List.iter statement block.statements in
  match written.kind with
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

let rec statement on_expression written =
  statement_parts ~expression:on_expression ~statement:(statement on_expression) written

let block on_expression (block : block) = List.iter (statement on_expression) block.statements

let children on_expression value =
  expression_parts ~expression:on_expression ~statement:(statement on_expression) value

let contains_break (body : block) =
  let has_break = ref false in
  let rec statement (written : statement) =
    match written.kind with
    | For _ | While _ -> ()
    | _ -> statement_parts ~expression ~statement written
  and expression (value : expression) =
    match value.kind with
    | Break -> has_break := true
    | Lambda _ -> ()
    | _ -> expression_parts ~expression ~statement value
  in
  List.iter statement body.statements;
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
  let block (written : block) =
    match visit with
    | Some visit -> List.iter visit written.statements
    | None -> block on_expression written
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
        (fun (member : trait_member line) ->
          match member.kind with
          | Associated_type (_, bounds) -> List.iter (path_type on_expression) bounds
          | Law law ->
              List.iter (parameter on_expression) law.parameters;
              List.iter on_expression law.requires;
              block law.body
          | Associated_capability _ | Trait_member_error -> ())
        members
  | Impl { trait_; type_; uses; members } ->
      path_type on_expression trait_;
      type_head on_expression type_;
      List.iter (capability_reference on_expression) uses;
      List.iter
        (fun (member : impl_member line) ->
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
      block body
  | Theorem { generics; parameters; clauses; body; _ } ->
      List.iter (generic_parameter on_expression) generics;
      List.iter (parameter on_expression) parameters;
      List.iter (clause on_expression) clauses;
      block body
  | Law_proof { trait_; type_; body; _ } ->
      path_type on_expression trait_;
      type_head on_expression type_;
      block body
  | Definition_error _ -> ()

let walk_names ?(on_path_type = ignore) ~on_name:add (definition_ : definition) =
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
    | Function_type { inputs; output; clauses; _ } ->
        List.iter
          (fun (input : function_input) ->
            Option.iter add input.name;
            type_ input.type_)
          inputs;
        Option.iter type_ output;
        List.iter clause_ clauses
    | Type_error -> ()
  and path_type_ (written : path_type) =
    on_path_type written;
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
  and capability_ (written : capability_reference) =
    match written.kind with
    | Capability_path written -> path_type_ written
    | Self_capabilities name -> add name
    | Associated_capabilities (base, name) ->
        add base;
        add name
  and clause_ (written : clause) =
    match written.kind with
    | Uses capabilities -> List.iter capability_ capabilities
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
    | For { pattern = bound; annotation; iterable; clauses; body; _ } ->
        Option.iter type_ annotation;
        expression iterable;
        pattern bound;
        List.iter (loop_clause expression) clauses;
        block_ body
    | _ -> statement_parts ~expression ~statement:statement_ written
  and block_ (written : block) = List.iter statement_ written.statements
  and pattern (written : pattern) =
    match written.kind with
    | Wildcard | Pattern_error -> ()
    | Binding name -> add name
    | Qualified_constant constant -> constant_ constant
    | Literal literal -> literal_ literal
    | Pattern_range { start; stop; _ } ->
        range_end start;
        range_end stop
    | Variant { name; fields } ->
        add name;
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
    | Some (Returns result | Lends (_, result)) -> type_ result
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
  | Method_declaration written -> signature_ written
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
          | Associated_type (name, bounds) ->
              add name;
              List.iter path_type_ bounds
          | Associated_capability name -> add name
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
      List.iter capability_ uses;
      List.iter
        (fun (member : impl_member line) ->
          match member.kind with
          | Associated_definition (name, written) ->
              add name;
              type_ written
          | Capability_definition (name, capabilities) ->
              add name;
              List.iter capability_ capabilities
          | Impl_member_error -> ())
        members
  | Capability { name; _ } -> add name
  | Constant { name; type_ = written; value } ->
      definition_name name;
      type_ written;
      expression value
  | Test { name; uses; body } ->
      literal_string name;
      List.iter capability_ uses;
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
      head written;
      block_ body
  | Definition_error { name; _ } -> Option.iter definition_name name

let spans (definition_ : definition) : span array =
  let spans = Array.make (definition_.id + 1) definition_.span in
  let rec pattern (written : pattern) =
    spans.(written.id) <- written.span;
    match written.kind with
    | Wildcard | Binding _ | Qualified_constant _ | Literal _ | Pattern_error -> ()
    | Pattern_range { start; stop; _ } ->
        spans.(start.id) <- start.span;
        spans.(stop.id) <- stop.span
    | Variant { fields; _ } -> Option.iter (List.iter pattern_field) fields
    | Record fields -> List.iter pattern_field fields
    | Alternatives alternatives -> List.iter pattern alternatives
  and pattern_field (written : pattern_field) =
    match written.kind with Named_field (_, inner) | Field inner -> pattern inner | Rest -> ()
  in
  let rec expression (value : expression) =
    spans.(value.id) <- value.span;
    (match value.kind with
    | Is { pattern = matched; _ } -> pattern matched
    | With (_, updates) ->
        List.iter (fun (update : update) -> spans.(update.id) <- update.span) updates
    | Quantified { binder = Binder_in (bound, _); _ } -> pattern bound
    | Lambda { parameters; _ } -> List.iter pattern parameters
    | Match { arms; _ } ->
        List.iter
          (fun (arm : arm) ->
            spans.(arm.id) <- arm.span;
            List.iter pattern arm.patterns)
          arms
    | _ -> ());
    expression_parts ~expression ~statement value
  and statement (written : statement) =
    spans.(written.id) <- written.span;
    (match written.kind with
    | Let { pattern = bound; _ } -> pattern bound
    | For { pattern = bound; clauses; _ } ->
        pattern bound;
        List.iter (fun (clause : loop_clause) -> spans.(clause.id) <- clause.span) clauses
    | While { clauses; _ } ->
        List.iter (fun (clause : loop_clause) -> spans.(clause.id) <- clause.span) clauses
    | _ -> ());
    statement_parts ~expression ~statement written
  in
  (match definition_.kind with
  | Function { signature = { clauses; _ }; _ }
  | Method_declaration { clauses; _ }
  | Theorem { clauses; _ } ->
      List.iter (fun (clause : clause) -> spans.(clause.id) <- clause.span) clauses
  | _ -> ());
  definition ~statement expression definition_;
  walk_names
    ~on_path_type:(fun (written : path_type) -> spans.(written.id) <- written.span)
    ~on_name:ignore definition_;
  spans

let names definition_ =
  let names = ref [] in
  walk_names ~on_name:(fun name -> names := name :: !names) definition_;
  List.stable_sort
    (fun (left : name) (right : name) -> compare left.span.start right.span.start)
    !names

let without_positions (definition_ : definition) : definition =
  let no_span = Span.zero_width 0 in
  let name_ (written : name) = { written with span = no_span } in
  let path (written : path) =
    { modules = List.map name_ written.modules; last = name_ written.last }
  in
  let rec type_ (written : type_expression) : type_expression =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Path_type written -> Path_type (path_type written)
        | Self_type name -> Self_type (Option.map name_ name)
        | Associated (base, name) -> Associated (name_ base, name_ name)
        | Any_type written -> Any_type (path_type written)
        | Function_type { inputs; output; clauses } ->
            Function_type
              {
                inputs =
                  List.map
                    (fun (input : function_input) ->
                      { input with name = Option.map name_ input.name; type_ = type_ input.type_ })
                    inputs;
                output = Option.map type_ output;
                clauses = List.map clause clauses;
              }
        | Type_error -> Type_error);
    }
  and path_type (written : path_type) =
    {
      written with
      path = path written.path;
      arguments = List.map type_argument written.arguments;
      span = no_span;
    }
  and type_argument = function
    | Type_argument written -> Type_argument (type_ written)
    | Count (value, _) -> Count (value, no_span)
    | Count_name written -> Count_name (name_ written)
    | Constraint (name, written) -> Constraint (name_ name, type_ written)
  and capability (written : capability_reference) : capability_reference =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Capability_path written -> Capability_path (path_type written)
        | Self_capabilities written -> Self_capabilities (name_ written)
        | Associated_capabilities (base, name) -> Associated_capabilities (name_ base, name_ name));
    }
  and clause (written : clause) : clause =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Uses capabilities -> Uses (List.map capability capabilities)
        | Requires value -> Requires (expression value)
        | Ensures value -> Ensures (expression value)
        | Decreases measures -> Decreases (List.map expression measures)
        | Cost written -> Cost (cost written)
        | Clause_error -> Clause_error);
    }
  and cost (written : cost) =
    {
      written with
      resource =
        (match written.resource with
        | Calls (Call_parameter written) -> Calls (Call_parameter (name_ written))
        | Calls (Call_capability written) -> Calls (Call_capability (path_type written))
        | Calls (Call_method (written, name)) -> Calls (Call_method (path_type written, name_ name))
        | (Time | Allocations | Allocated_bytes) as resource -> resource);
      bound =
        (match written.bound with
        | Big_o value -> Big_o (expression value)
        | At_most value -> At_most (expression value)
        | Exactly value -> Exactly (expression value)
        | Finite -> Finite);
    }
  and string_literal (written : string_literal) =
    {
      written with
      tag = Option.map path written.tag;
      first = text written.first;
      rest = List.map (fun (value, rest) -> (expression value, text rest)) written.rest;
      span = no_span;
    }
  and text (written : text) = { written with span = no_span }
  and expression (written : expression) : expression =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | ( Integer _ | Float _ | True | False | Todo | Unreachable | Break | Continue | Self_value
          | Self_type_value | Expression_error ) as kind ->
            kind
        | String literal -> String (string_literal literal)
        | Name written -> Name (path written)
        | Member (base, name) -> Member (expression base, name_ name)
        | Bracket (base, items) ->
            Bracket
              ( expression base,
                List.map
                  (function
                    | Item item -> Item (expression item)
                    | Item_constraint (name, written) -> Item_constraint (name_ name, type_ written))
                  items )
        | Call (callee, arguments) ->
            Call
              ( expression callee,
                List.map
                  (fun (argument : argument) ->
                    { label = Option.map name_ argument.label; value = expression argument.value })
                  arguments )
        | Try value -> Try (expression value)
        | With (base, updates) -> With (expression base, List.map update updates)
        | Prefix (operator, value) -> Prefix (operator, expression value)
        | Mode (mode, value) -> Mode (mode, expression value)
        | Any value -> Any (expression value)
        | Binary { operator; left; right; _ } ->
            Binary
              {
                operator;
                operator_span = no_span;
                left = expression left;
                right = expression right;
              }
        | Is { value; pattern = matched; _ } ->
            Is { value = expression value; operator_span = no_span; pattern = pattern matched }
        | Range { start; stop; inclusive; _ } ->
            Range
              {
                start = Option.map expression start;
                operator_span = no_span;
                stop = Option.map expression stop;
                inclusive;
              }
        | Quantified { quantifier; binder; body } ->
            Quantified
              {
                quantifier;
                binder =
                  (match binder with
                  | Binder_in (bound, collection) -> Binder_in (pattern bound, expression collection)
                  | Binder_type (name, written) -> Binder_type (name_ name, type_ written));
                body = expression body;
              }
        | Echo value -> Echo (expression value)
        | Return value -> Return (Option.map expression value)
        | Parenthesized value -> Parenthesized (expression value)
        | List values -> List (List.map expression values)
        | Map pairs -> Map (List.map (fun (key, value) -> (expression key, expression value)) pairs)
        | Lambda { parameters; body } ->
            Lambda { parameters = List.map pattern parameters; body = block body }
        | If { condition; then_; else_ } ->
            If
              {
                condition = expression condition;
                then_ = block then_;
                else_ =
                  Option.map
                    (function
                      | Else written -> Else (block written)
                      | Else_if value -> Else_if (expression value))
                    else_;
              }
        | Match { scrutinees; arms } ->
            Match { scrutinees = List.map expression scrutinees; arms = List.map arm arms }
        | Provide { implementations; body } ->
            Provide { implementations = List.map expression implementations; body = block body }
        | Block written -> Block (block written));
    }
  and update (written : update) : update =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Update { field; path = rest; value } ->
            Update
              {
                field = name_ field;
                path = List.map name_ rest;
                value = Option.map expression value;
              }
        | Update_error -> Update_error);
    }
  and arm (written : arm) =
    {
      written with
      patterns = List.map pattern written.patterns;
      guard = Option.map expression written.guard;
      body = statement written.body;
      span = no_span;
      blank_line_before = false;
    }
  and block (written : block) =
    { written with statements = List.map statement written.statements; span = no_span }
  and statement (written : statement) : statement =
    {
      written with
      span = no_span;
      blank_line_before = false;
      kind =
        (match written.kind with
        | Let { is_var; pattern = bound; annotation; value; else_ } ->
            Let
              {
                is_var;
                pattern = pattern bound;
                annotation = Option.map type_ annotation;
                value = expression value;
                else_ = Option.map block else_;
              }
        | Expression value -> Expression (expression value)
        | Assignment { target; operator; value } ->
            Assignment { target = expression target; operator; value = expression value }
        | For { mode; pattern = bound; annotation; iterable; clauses; body } ->
            For
              {
                mode;
                pattern = pattern bound;
                annotation = Option.map type_ annotation;
                iterable = expression iterable;
                clauses = List.map loop_clause clauses;
                body = block body;
              }
        | While { condition; clauses; body } ->
            While
              {
                condition = expression condition;
                clauses = List.map loop_clause clauses;
                body = block body;
              }
        | Parallel written -> Parallel (block written)
        | Concurrent written -> Concurrent (block written)
        | Proof written -> Proof (block written)
        | Assert { value; by_bit_vector } -> Assert { value = expression value; by_bit_vector }
        | Statement_error -> Statement_error);
    }
  and loop_clause (written : loop_clause) : loop_clause =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Invariant value -> Invariant (expression value)
        | Loop_decreases measures -> Loop_decreases (List.map expression measures)
        | Loop_cost written -> Loop_cost (cost written));
    }
  and pattern (written : pattern) : pattern =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | (Wildcard | Pattern_error) as kind -> kind
        | Binding name -> Binding (name_ name)
        | Qualified_constant written -> Qualified_constant (constant written)
        | Literal written -> Literal (literal written)
        | Pattern_range { start; stop; inclusive } ->
            Pattern_range { start = range_end start; stop = range_end stop; inclusive }
        | Variant { name; fields } ->
            Variant { name = name_ name; fields = Option.map (List.map pattern_field) fields }
        | Record fields -> Record (List.map pattern_field fields)
        | Alternatives alternatives -> Alternatives (List.map pattern alternatives));
    }
  and constant = function
    | Module_constant written -> Module_constant (path written)
    | Type_constant (written, name) -> Type_constant (path written, name_ name)
  and literal = function
    | Literal_string written -> Literal_string (string_literal written)
    | (Literal_integer _ | Literal_true | Literal_false) as written -> written
  and range_end (written : range_end) : range_end =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | End_literal written -> End_literal (literal written)
        | End_constant written -> End_constant (constant written));
    }
  and pattern_field (written : pattern_field) : pattern_field =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Named_field (name, inner) -> Named_field (name_ name, pattern inner)
        | Field inner -> Field (pattern inner)
        | Rest -> Rest);
    }
  in
  let generic (written : generic_parameter) : generic_parameter =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Type_parameter (name, bounds) -> Type_parameter (name_ name, List.map path_type bounds)
        | Value_parameter (name, written) -> Value_parameter (name_ name, type_ written)
        | Capability_parameter name -> Capability_parameter (name_ name)
        | Generic_error -> Generic_error);
    }
  in
  let head (written : type_head) =
    {
      written with
      path = path written.path;
      generics = List.map generic written.generics;
      span = no_span;
    }
  in
  let definition_name = function
    | Plain_name name -> Plain_name (name_ name)
    | Member_name (written, name) -> Member_name (head written, name_ name)
  in
  let parameter (written : parameter) : parameter =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Named_parameter { name; mode; type_ = written; default } ->
            Named_parameter
              {
                name = name_ name;
                mode;
                type_ = type_ written;
                default = Option.map expression default;
              }
        | (Self_parameter _ | Parameter_error) as kind -> kind);
    }
  in
  let signature (written : signature) =
    {
      name = definition_name written.name;
      generics = List.map generic written.generics;
      parameters = List.map parameter written.parameters;
      result =
        Option.map
          (function
            | Returns result -> Returns (type_ result)
            | Lends (mode, result) -> Lends (mode, type_ result))
          written.result;
      clauses = List.map clause written.clauses;
    }
  in
  let field (written : field) : field =
    {
      written with
      span = no_span;
      kind =
        (match written.kind with
        | Field_declaration { name; type_ = written; default } ->
            Field_declaration
              { name = name_ name; type_ = type_ written; default = Option.map expression default }
        | Field_error -> Field_error);
    }
  in
  let line (written : _ line) kind =
    { written with kind; span = no_span; blank_line_before = false }
  in
  let kind : definition_kind =
    match definition_.kind with
    | Function { signature = written; body } ->
        Function { signature = signature written; body = block body }
    | Method_declaration written -> Method_declaration (signature written)
    | Type_definition { name; generics; body; clauses } ->
        Type_definition
          {
            name = name_ name;
            generics = List.map generic generics;
            body =
              (match body with
              | Fields written -> Fields (List.map field written)
              | Variants variants ->
                  Variants
                    (List.map
                       (fun (variant : variant) ->
                         {
                           variant with
                           name = name_ variant.name;
                           fields = Option.map (List.map field) variant.fields;
                           span = no_span;
                         })
                       variants)
              | Type_todo -> Type_todo);
            clauses =
              List.map
                (fun (written : type_clause) : type_clause ->
                  {
                    written with
                    span = no_span;
                    kind =
                      (match written.kind with
                      | Type_invariant value -> Type_invariant (expression value)
                      | Derives traits -> Derives (List.map path_type traits)
                      | Potential value -> Potential (expression value));
                  })
                clauses;
          }
    | Trait { name; generics; requires; members } ->
        Trait
          {
            name = name_ name;
            generics = List.map generic generics;
            requires = List.map path_type requires;
            members =
              List.map
                (fun (member : trait_member line) ->
                  line member
                    (match member.kind with
                    | Associated_type (name, bounds) ->
                        Associated_type (name_ name, List.map path_type bounds)
                    | Associated_capability name -> Associated_capability (name_ name)
                    | Law law ->
                        Law
                          {
                            name = name_ law.name;
                            parameters = List.map parameter law.parameters;
                            requires = List.map expression law.requires;
                            body = block law.body;
                          }
                    | Trait_member_error -> Trait_member_error))
                members;
          }
    | Impl { trait_; type_ = written; uses; members } ->
        Impl
          {
            trait_ = path_type trait_;
            type_ = head written;
            uses = List.map capability uses;
            members =
              List.map
                (fun (member : impl_member line) ->
                  line member
                    (match member.kind with
                    | Associated_definition (name, written) ->
                        Associated_definition (name_ name, type_ written)
                    | Capability_definition (name, capabilities) ->
                        Capability_definition (name_ name, List.map capability capabilities)
                    | Impl_member_error -> Impl_member_error))
                members;
          }
    | Capability { name; members } ->
        Capability
          {
            name = name_ name;
            members =
              List.map (fun (member : capability_member line) -> line member member.kind) members;
          }
    | Constant { name; type_ = written; value } ->
        Constant { name = definition_name name; type_ = type_ written; value = expression value }
    | Test { name; uses; body } ->
        Test { name = string_literal name; uses = List.map capability uses; body = block body }
    | Theorem { name; generics; parameters; clauses; body } ->
        Theorem
          {
            name = name_ name;
            generics = List.map generic generics;
            parameters = List.map parameter parameters;
            clauses = List.map clause clauses;
            body = block body;
          }
    | Law_proof { trait_; law; type_ = written; body } ->
        Law_proof
          { trait_ = path_type trait_; law = name_ law; type_ = head written; body = block body }
    | Definition_error { intended; name } ->
        Definition_error { intended; name = Option.map definition_name name }
  in
  {
    definition_ with
    kind;
    span = no_span;
    recovered = List.map (fun _ -> no_span) definition_.recovered;
  }

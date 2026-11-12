open Syntax

let rec type_expression on_expression (type_ : type_expression) =
  match type_.kind with
  | Path_type path -> path_type on_expression path
  | Any_type path -> path_type on_expression path
  | Function_type { inputs; output; clauses; _ } ->
      List.iter (fun (_, input) -> type_expression on_expression input) inputs;
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
  | Expression value | Assert value | Yield value -> on_expression value
  | Assignment { target; value; _ } ->
      on_expression target;
      on_expression value
  | For { iterable; clauses; body; _ } ->
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
  | Some (Returns type_ | Yields (_, type_) | Lends (_, type_)) ->
      type_expression on_expression type_
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

let spans (definition_ : definition) : span array =
  let spans = Array.make (definition_.id + 1) definition_.span in
  let rec pattern (written : pattern) =
    spans.(written.id) <- written.span;
    match written.kind with
    | Wildcard | Binding_or_constant _ | Qualified_constant _ | Literal _ | Pattern_error -> ()
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
  spans

(* Visits names in expressions, patterns, types, clauses, and heads. *)
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
    | Function_type { inputs; output; clauses; _ } ->
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

let names definition_ =
  let names = ref [] in
  walk_names ~on_name:(fun name -> names := name :: !names) definition_;
  List.stable_sort
    (fun (left : name) (right : name) -> compare left.span.start right.span.start)
    !names

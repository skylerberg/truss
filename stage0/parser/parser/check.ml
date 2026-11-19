type enclosing_loop = No_loop | In_loop | Across_lambda | Across_parallel_branch | In_parallel_for

type context = {
  is_specification : bool;
  allows_assert : bool;
  is_function_body : bool;
  enclosing_loop : enclosing_loop;
  is_in_parallel : bool;
}

let plain =
  {
    is_specification = false;
    allows_assert = false;
    is_function_body = false;
    enclosing_loop = No_loop;
    is_in_parallel = false;
  }

let enter_specification context = { context with is_specification = true }
let enter_proof context = { context with is_specification = true; allows_assert = true }
let may_be_specification context = context.is_specification || context.is_function_body
let show_quantifier = function Language.Quantifier.Forall -> "forall" | Exists -> "exists"

let report cursor code id message =
  Cursor.report cursor code (Cursor.read_file_span cursor id) message

let try_operator_span cursor id =
  let span = Cursor.read_span cursor id in
  Cursor.make_file_span cursor
    (Source.Definition_span.make (max span.start (span.stop - 1)) span.stop)

let rec check_expression cursor context (value : Syntax.expression) =
  (match value.kind with
  | Quantified { quantifier; binder = Binder_type _; _ } when not (may_be_specification context) ->
      report cursor Specification_only value.id
        (Printf.sprintf
           "`%s` over a whole type cannot run, so it is only for specifications and the bodies of \
            functions for specifications only. Quantify over a range or a collection, as in `%s i \
            in 0..count => ...`."
           (show_quantifier quantifier) (show_quantifier quantifier))
  | Binary { operator = Connective Implies; operator_id; _ } when not (may_be_specification context)
    ->
      report cursor Specification_only operator_id
        "`==>` is only for specifications and the bodies of functions for specifications only; in \
         code, write `!a || b`."
  | Echo _ when context.is_specification ->
      report cursor Echo_in_specification value.id
        "`echo` is not allowed in specifications, which never run."
  | Try _ when context.is_in_parallel ->
      Cursor.report cursor Exits_parallel
        (try_operator_span cursor value.id)
        "`?` cannot exit a `parallel` block or a `parallel for`; return a `Result` from the branch \
         and use `?` after it."
  | Return _ when context.is_in_parallel ->
      report cursor Exits_parallel value.id
        "`return` cannot exit a `parallel` block or a `parallel for`."
  | Break | Continue -> check_loop_exit cursor context value
  | _ -> ());
  match value.kind with
  | Lambda { body; _ } ->
      let enclosing_loop =
        match context.enclosing_loop with No_loop -> No_loop | _ -> Across_lambda
      in
      check_block cursor
        { context with allows_assert = false; is_in_parallel = false; enclosing_loop }
        body
  | _ -> check_parts cursor context value

and check_parts cursor context value =
  Syntax_walk.visit_expression_parts ~on_expression:(check_expression cursor context)
    ~on_statement:(check_statement cursor context) value

and check_loop_exit cursor context (value : Syntax.expression) =
  let word = match value.kind with Break -> "break" | _ -> "continue" in
  match (context.enclosing_loop, value.kind) with
  | In_loop, _ | In_parallel_for, Continue -> ()
  | No_loop, _ ->
      report cursor Misplaced_loop_exit value.id
        (Printf.sprintf "`%s` is only allowed in a loop." word)
  | Across_lambda, _ ->
      report cursor Misplaced_loop_exit value.id
        (Printf.sprintf "`%s` cannot reach a loop outside the lambda it is in." word)
  | In_parallel_for, _ ->
      report cursor Exits_parallel value.id "`break` cannot exit a `parallel for`; `continue` can."
  | Across_parallel_branch, _ ->
      report cursor Exits_parallel value.id
        (Printf.sprintf "`%s` cannot leave a branch of a `parallel` block." word)

and check_block cursor context (body : Syntax.block) =
  List.iter (check_statement cursor context) body.statements

and check_types ?(parameter = false) cursor context type_ =
  check_placement cursor ~top:parameter type_;
  Syntax_walk.visit_type_expression (check_expression cursor (enter_specification context)) type_

and check_placement cursor ~top (type_ : Syntax.type_expression) =
  match type_.kind with
  | Function_type { inputs; output; clauses; _ } ->
      if not top then
        List.iter
          (fun (clause : Syntax.clause) ->
            match clause.kind with
            | Requires _ ->
                report cursor Misplaced_requires clause.id
                  "A function type has a `requires` only as the type of a parameter, where it \
                   constrains the arguments the callee passes its callback."
            | _ -> ())
          clauses;
      List.iter
        (fun (input : Syntax.function_input) -> check_placement cursor ~top:false input.type_)
        inputs;
      Option.iter (check_placement cursor ~top:false) output
  | Path_type path | Any_type path -> check_path_placement cursor path
  | Self_type _ | Associated _ | Type_error -> ()

and check_path_placement cursor (path : Syntax.path_type) =
  List.iter
    (function
      | Syntax.Type_argument type_ | Constraint (_, type_) ->
          check_placement cursor ~top:false type_
      | Count _ | Count_name _ -> ())
    path.arguments

and check_loop_clauses cursor context clauses =
  List.iter
    (Syntax_walk.visit_loop_clause (check_expression cursor (enter_specification context)))
    clauses

and check_statement cursor context (statement : Syntax.statement) =
  match statement.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (check_types cursor context) annotation;
      check_expression cursor context value;
      Option.iter (check_block cursor context) else_
  | For { mode; annotation; iterable; clauses; body; _ } ->
      Option.iter (check_types cursor context) annotation;
      check_expression cursor context iterable;
      check_loop_clauses cursor context clauses;
      let body_context =
        match mode with
        | Parallel -> { context with enclosing_loop = In_parallel_for; is_in_parallel = true }
        | Sequential -> { context with enclosing_loop = In_loop }
        | Concurrent -> { context with enclosing_loop = In_loop }
      in
      check_block cursor body_context body
  | While { condition; clauses; body } ->
      check_expression cursor context condition;
      check_loop_clauses cursor context clauses;
      check_block cursor { context with enclosing_loop = In_loop } body
  | Parallel body ->
      let enclosing_loop =
        match context.enclosing_loop with No_loop -> No_loop | _ -> Across_parallel_branch
      in
      check_block cursor { context with is_in_parallel = true; enclosing_loop } body
  | Concurrent body -> check_block cursor context body
  | Proof body ->
      if not context.is_function_body then
        report cursor Misplaced_proof statement.id
          "A `proof` block is only allowed in a function's body.";
      check_block cursor (enter_proof context) body
  | Assert _ ->
      if not context.allows_assert then
        report cursor Misplaced_assert statement.id
          "`assert` is only allowed in tests, theorems, and proofs.";
      check_statement_parts cursor context statement
  | Expression _ | Assignment _ | Statement_error -> check_statement_parts cursor context statement

and check_statement_parts cursor context (parent : Syntax.statement) =
  Syntax_walk.visit_statement_parts ~on_expression:(check_expression cursor context)
    ~on_statement:(check_statement cursor context) parent

let check_parameters ?(lends = false) cursor (parameters : Syntax.parameter list) =
  List.iter
    (fun (parameter : Syntax.parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_; default; _ } ->
          if name.text = "result" then
            report cursor Reserved_specification_name name.id
              "A parameter cannot be named `result`, which names the return value in `ensures` and \
               `cost`.";
          if lends && name.text = "final" then
            report cursor Reserved_specification_name name.id
              "A parameter of a lending method cannot be named `final`: in the method's `ensures`, \
               `final(result)` is the part as the caller left it.";
          check_types ~parameter:true cursor plain type_;
          Option.iter (check_expression cursor plain) default
      | Self_parameter _ | Parameter_error -> ())
    parameters

let rec check_trait_arguments cursor ~is_law_proof (trait_ : Syntax.path_type) =
  List.iter
    (function
      | Syntax.Type_argument type_ | Constraint (_, type_) ->
          check_trait_argument cursor ~is_law_proof type_
      | Count _ | Count_name _ -> ())
    trait_.arguments

and check_trait_argument cursor ~is_law_proof (type_ : Syntax.type_expression) =
  let report_associated_type written =
    report cursor Misplaced_associated_type type_.id
      (if is_law_proof then
         Printf.sprintf
           "`%s` cannot be a trait argument of a law proof, since no `impl` can have one." written
       else
         Printf.sprintf
           "`%s` cannot be a trait argument of an `impl`: an associated type may stand for any \
            type, so the `impl` could overlap every other `impl` of the trait for its type."
           written)
  in
  match type_.kind with
  | Path_type path | Any_type path -> check_trait_arguments cursor ~is_law_proof path
  | Function_type _ ->
      report cursor Misplaced_function_type type_.id
        (if is_law_proof then
           "A function type cannot be a trait argument of a law proof, since no `impl` can have \
            one."
         else
           "A function type cannot be a trait argument of an `impl`. Use a record that holds the \
            function, such as `type Callback(run: fn(Int64) -> Int64)`, as the argument.")
  | Associated (parameter, name) -> report_associated_type (parameter.text ^ "." ^ name.text)
  | Self_type (Some name) -> report_associated_type ("Self." ^ name.text)
  | Self_type None | Type_error -> ()

let check_header_trait cursor ~is_law_proof (trait_ : Syntax.path_type) =
  List.iter
    (function
      | Syntax.Constraint (name, type_) ->
          let span =
            Cursor.make_file_span cursor
              (Source.Definition_span.make (Cursor.read_span cursor name.id).start
                 (Cursor.read_span cursor type_.id).stop)
          in
          let written = Option.value ~default:name.text (Cursor.spell cursor span) in
          Cursor.report cursor Misplaced_constraint span
            (if is_law_proof then
               Printf.sprintf
                 "A law proof's trait takes no constraint such as `%s`: the `impl` it proves \
                  chooses `%s` in its body."
                 written name.text
             else
               Printf.sprintf
                 "An `impl` chooses its associated types in its body, so `%s` on its trait would \
                  have no effect. Write `type %s = %s` in the `impl` instead."
                 written name.text
                 (Option.value ~default:"..."
                    (Cursor.spell cursor (Cursor.read_file_span cursor type_.id))))
      | Type_argument _ | Count _ | Count_name _ -> ())
    trait_.arguments;
  check_trait_arguments cursor ~is_law_proof trait_

let check_clauses cursor clauses =
  List.iter (Syntax_walk.visit_clause (check_expression cursor (enter_specification plain))) clauses

let check_generic_parameters cursor generics =
  List.iter
    (Syntax_walk.visit_generic_parameter (check_expression cursor (enter_specification plain)))
    generics

let check_function_name cursor (name : Syntax.definition_name) =
  let name = match name with Plain_name name | Member_name (_, name) -> name in
  if name.text = "old" then
    report cursor Reserved_specification_name name.id
      "A function cannot be named `old`, which names a value as it was when a function was called, \
       in specifications."
  else if name.text = "identical" then
    report cursor Reserved_specification_name name.id
      "A function cannot be named `identical`, which tests whether two values are the same value, \
       in specifications."

let check_signature cursor (signature : Syntax.signature) =
  check_function_name cursor signature.name;
  Syntax_walk.visit_definition_name
    (check_expression cursor (enter_specification plain))
    signature.name;
  check_generic_parameters cursor signature.generics;
  let lends = match signature.result with Some (Lends _) -> true | _ -> false in
  check_parameters ~lends cursor signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Lends (_, type_)) -> check_types cursor plain type_
  | None -> ());
  check_clauses cursor signature.clauses

let check_function_definition cursor (definition : Syntax.function_definition) =
  check_signature cursor definition.signature;
  check_block cursor { plain with is_function_body = true } definition.body

let check_fields cursor (fields : Syntax.field list) =
  List.iter
    (fun (field : Syntax.field) ->
      match field.kind with
      | Field_declaration { type_; default; _ } ->
          check_types cursor plain type_;
          Option.iter (check_expression cursor plain) default
      | Field_error -> ())
    fields

let check_definition cursor (definition : Syntax.definition) =
  match definition.kind with
  | Function function_ -> check_function_definition cursor function_
  | Method_declaration declared -> check_signature cursor declared
  | Type_definition { generics; body; clauses; _ } ->
      check_generic_parameters cursor generics;
      (match body with
      | Fields list -> check_fields cursor list
      | Variants variants ->
          List.iter
            (fun (variant : Syntax.variant) -> Option.iter (check_fields cursor) variant.fields)
            variants
      | Type_todo -> ());
      List.iter
        (fun (clause : Syntax.type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value ->
              check_expression cursor (enter_specification plain) value
          | Derives _ -> ())
        clauses
  | Trait { generics; members; _ } ->
      check_generic_parameters cursor generics;
      List.iter
        (fun (member : Syntax.trait_member Syntax.node) ->
          match member.kind with
          | Law law ->
              check_parameters cursor law.parameters;
              List.iter (check_expression cursor (enter_specification plain)) law.requires;
              check_block cursor (enter_specification plain) law.body
          | Associated_type _ | Associated_capability _ | Trait_member_error -> ())
        members
  | Impl { trait_; type_; members; _ } ->
      check_header_trait cursor ~is_law_proof:false trait_;
      check_generic_parameters cursor type_.generics;
      List.iter
        (fun (member : Syntax.impl_member Syntax.node) ->
          match member.kind with
          | Associated_definition (_, type_) -> check_types cursor plain type_
          | Capability_definition _ | Impl_member_error -> ())
        members
  | Capability _ -> ()
  | Constant { type_; value; _ } ->
      check_types cursor plain type_;
      check_expression cursor plain value
  | Test { body; _ } -> check_block cursor { plain with allows_assert = true } body
  | Theorem { generics; parameters = theorem_parameters; clauses = theorem_clauses; body; _ } ->
      check_generic_parameters cursor generics;
      check_parameters cursor theorem_parameters;
      check_clauses cursor theorem_clauses;
      check_block cursor (enter_proof plain) body
  | Law_proof { trait_; type_; body; _ } ->
      check_header_trait cursor ~is_law_proof:true trait_;
      check_generic_parameters cursor type_.generics;
      check_block cursor (enter_proof plain) body
  | Definition_error _ -> ()

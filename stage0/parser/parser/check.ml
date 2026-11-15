open Syntax

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

let specification context = { context with is_specification = true }
let proof context = { context with is_specification = true; allows_assert = true }
let may_be_specification context = context.is_specification || context.is_function_body
let quantifier_word = function Forall -> "forall" | Exists -> "exists"

let report cursor code id message =
  Cursor.report cursor code (Cursor.read_file_span cursor id) message

let try_operator_span cursor id =
  let span = Cursor.read_span cursor id in
  Cursor.file_span cursor (Source.Definition_span.make (max span.start (span.stop - 1)) span.stop)

let rec expression cursor context (value : expression) =
  (match value.kind with
  | Quantified { quantifier; binder = Binder_type _; _ } when not (may_be_specification context) ->
      report cursor Specification_only value.id
        (Printf.sprintf
           "`%s` over a whole type cannot run, so it is only for specifications and the bodies of \
            functions for specifications only. Quantify over a range or a collection, as in `%s i \
            in 0..count => ...`."
           (quantifier_word quantifier) (quantifier_word quantifier))
  | Binary { operator = Implies; operator_id; _ } when not (may_be_specification context) ->
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
  | Break | Continue -> loop_exit cursor context value
  | _ -> ());
  match value.kind with
  | Lambda { body; _ } ->
      let enclosing_loop =
        match context.enclosing_loop with No_loop -> No_loop | _ -> Across_lambda
      in
      block cursor
        { context with allows_assert = false; is_in_parallel = false; enclosing_loop }
        body
  | _ -> parts cursor context value

and parts cursor context value =
  Syntax_walk.expression_parts ~expression:(expression cursor context)
    ~statement:(statement cursor context) value

and loop_exit cursor context (value : expression) =
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

and block cursor context (body : block) = List.iter (statement cursor context) body.statements

and types ?(parameter = false) cursor context type_ =
  requires_placement cursor ~top:parameter type_;
  Syntax_walk.type_expression (expression cursor (specification context)) type_

and requires_placement cursor ~top (type_ : type_expression) =
  match type_.kind with
  | Function_type { inputs; output; clauses; _ } ->
      if not top then
        List.iter
          (fun (clause : clause) ->
            match clause.kind with
            | Requires _ ->
                report cursor Misplaced_requires clause.id
                  "A function type has a `requires` only as the type of a parameter, where it \
                   constrains the arguments the callee passes its callback."
            | _ -> ())
          clauses;
      List.iter
        (fun (input : function_input) -> requires_placement cursor ~top:false input.type_)
        inputs;
      Option.iter (requires_placement cursor ~top:false) output
  | Path_type path | Any_type path -> path_requires_placement cursor path
  | Self_type _ | Associated _ | Type_error -> ()

and path_requires_placement cursor (path : path_type) =
  List.iter
    (function
      | Type_argument type_ | Constraint (_, type_) -> requires_placement cursor ~top:false type_
      | Count _ | Count_name _ -> ())
    path.arguments

and loop_clauses cursor context clauses =
  List.iter (Syntax_walk.loop_clause (expression cursor (specification context))) clauses

and statement cursor context (statement : statement) =
  match statement.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (types cursor context) annotation;
      expression cursor context value;
      Option.iter (block cursor context) else_
  | For { mode; annotation; iterable; clauses; body; _ } ->
      Option.iter (types cursor context) annotation;
      expression cursor context iterable;
      loop_clauses cursor context clauses;
      let body_context =
        match mode with
        | Parallel_loop -> { context with enclosing_loop = In_parallel_for; is_in_parallel = true }
        | Sequential -> { context with enclosing_loop = In_loop }
        | Concurrent_loop -> { context with enclosing_loop = In_loop }
      in
      block cursor body_context body
  | While { condition; clauses; body } ->
      expression cursor context condition;
      loop_clauses cursor context clauses;
      block cursor { context with enclosing_loop = In_loop } body
  | Parallel body ->
      let enclosing_loop =
        match context.enclosing_loop with No_loop -> No_loop | _ -> Across_parallel_branch
      in
      block cursor { context with is_in_parallel = true; enclosing_loop } body
  | Concurrent body -> block cursor context body
  | Proof body ->
      if not context.is_function_body then
        report cursor Misplaced_proof statement.id
          "A `proof` block is only allowed in a function's body.";
      block cursor (proof context) body
  | Assert _ ->
      if not context.allows_assert then
        report cursor Misplaced_assert statement.id
          "`assert` is only allowed in tests, theorems, and proofs.";
      statement_parts cursor context statement
  | Expression _ | Assignment _ | Statement_error -> statement_parts cursor context statement

and statement_parts cursor context (parent : statement) =
  Syntax_walk.statement_parts ~expression:(expression cursor context)
    ~statement:(statement cursor context) parent

let parameters ?(lends = false) cursor (parameters : parameter list) =
  List.iter
    (fun (parameter : parameter) ->
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
          types ~parameter:true cursor plain type_;
          Option.iter (expression cursor plain) default
      | Self_parameter _ | Parameter_error -> ())
    parameters

let clauses cursor clauses =
  List.iter (Syntax_walk.clause (expression cursor (specification plain))) clauses

let generic_parameters cursor generics =
  List.iter (Syntax_walk.generic_parameter (expression cursor (specification plain))) generics

let function_name cursor (name : definition_name) =
  let name = match name with Plain_name name | Member_name (_, name) -> name in
  if name.text = "old" then
    report cursor Reserved_specification_name name.id
      "A function cannot be named `old`, which names a value as it was when a function was called, \
       in specifications."
  else if name.text = "identical" then
    report cursor Reserved_specification_name name.id
      "A function cannot be named `identical`, which tests whether two values are the same value, \
       in specifications."

let signature cursor (signature : signature) =
  function_name cursor signature.name;
  Syntax_walk.definition_name (expression cursor (specification plain)) signature.name;
  generic_parameters cursor signature.generics;
  let lends = match signature.result with Some (Lends _) -> true | _ -> false in
  parameters ~lends cursor signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Lends (_, type_)) -> types cursor plain type_
  | None -> ());
  clauses cursor signature.clauses

let function_ cursor (declared : signature) body =
  signature cursor declared;
  Option.iter (block cursor { plain with is_function_body = true }) body

let function_definition cursor (definition : function_definition) =
  function_ cursor definition.signature (Some definition.body)

let fields cursor (fields : field list) =
  List.iter
    (fun (field : field) ->
      match field.kind with
      | Field_declaration { type_; default; _ } ->
          types cursor plain type_;
          Option.iter (expression cursor plain) default
      | Field_error -> ())
    fields

let definition cursor (definition : definition) =
  match definition.kind with
  | Function function_ -> function_definition cursor function_
  | Method_declaration declared -> signature cursor declared
  | Type_definition { generics; body; clauses; _ } ->
      generic_parameters cursor generics;
      (match body with
      | Fields list -> fields cursor list
      | Variants variants ->
          List.iter (fun (variant : variant) -> Option.iter (fields cursor) variant.fields) variants
      | Type_todo -> ());
      List.iter
        (fun (clause : type_clause) ->
          match clause.kind with
          | Type_invariant value | Potential value -> expression cursor (specification plain) value
          | Derives _ -> ())
        clauses
  | Trait { generics; members; _ } ->
      generic_parameters cursor generics;
      List.iter
        (fun (member : trait_member node) ->
          match member.kind with
          | Law law ->
              parameters cursor law.parameters;
              List.iter (expression cursor (specification plain)) law.requires;
              block cursor (specification plain) law.body
          | Associated_type _ | Associated_capability _ | Trait_member_error -> ())
        members
  | Impl { type_; members; _ } ->
      generic_parameters cursor type_.generics;
      List.iter
        (fun (member : impl_member node) ->
          match member.kind with
          | Associated_definition (_, type_) -> types cursor plain type_
          | Capability_definition _ | Impl_member_error -> ())
        members
  | Capability _ -> ()
  | Constant { type_; value; _ } ->
      types cursor plain type_;
      expression cursor plain value
  | Test { body; _ } -> block cursor { plain with allows_assert = true } body
  | Theorem { generics; parameters = theorem_parameters; clauses = theorem_clauses; body; _ } ->
      generic_parameters cursor generics;
      parameters cursor theorem_parameters;
      clauses cursor theorem_clauses;
      block cursor (proof plain) body
  | Law_proof { type_; body; _ } ->
      generic_parameters cursor type_.generics;
      block cursor (proof plain) body
  | Definition_error _ -> ()

(* The rules that need the whole tree of one definition: where
   specification-only forms, [assert], [proof], [break], [continue],
   [return], [?], and [echo] may appear.

   This is a separate walk with a small context, so the parsing code does
   not thread a context through every call, and each rule is tested on its
   own. *)

open Syntax

type loop =
  | Outside  (** No loop around this point. *)
  | Inside  (** In a loop's body. *)
  | Across_lambda  (** In a lambda inside a loop's body. *)
  | Parallel_body  (** In the body of a [parallel for]. *)
  | Branch  (** In a branch of a [parallel] block inside a loop. *)

type context = {
  specification : bool;
      (** [requires], [ensures], invariants, [decreases], [cost], laws, theorems, proofs *)
  assert_allowed : bool;  (** Tests, theorems, and proofs, outside lambdas *)
  function_body : bool;
      (** In a function's body, where a [proof] block may appear, and where [==>] and a quantifier
          over a type are left to the type checker, which knows whether the function is for
          specifications only *)
  loop : loop;
  in_parallel : bool;
      (** In a [parallel] branch or a [parallel for] body, where [return] and [?] cannot leave *)
}

let plain =
  {
    specification = false;
    assert_allowed = false;
    function_body = false;
    loop = Outside;
    in_parallel = false;
  }

let specification context = { context with specification = true }
let proof context = { context with specification = true; assert_allowed = true }

(* Where [==>] and a quantifier over a type may appear as far as the parser
   can tell. In a function's body, only the type checker knows whether the
   function is for specifications only. *)
let may_be_specification context = context.specification || context.function_body
let quantifier_word = function Forall -> "forall" | Exists -> "exists"

let report cursor code (span : span) message =
  Cursor.report cursor code (Cursor.absolute cursor span) message

(* The last byte of a span, where the [?] of [x?] is. *)
let last_byte (span : span) = Syntax.Span.make (max span.start (span.stop - 1)) span.stop

let rec expression cursor context (value : expression) =
  (match value.kind with
  | Quantified { quantifier; binder = Binder_type _; _ } when not (may_be_specification context) ->
      report cursor Specification_only value.span
        (Printf.sprintf
           "`%s` over a whole type cannot run, so it is only for specifications and the bodies of \
            functions for specifications only. Quantify over a range or a collection, as in `%s i \
            in 0..count => ...`."
           (quantifier_word quantifier) (quantifier_word quantifier))
  | Binary { operator = Implies; operator_span; _ } when not (may_be_specification context) ->
      report cursor Specification_only operator_span
        "`==>` is only for specifications and the bodies of functions for specifications only; in \
         code, write `!a || b`."
  | Echo _ when context.specification ->
      report cursor Echo_in_specification value.span
        "`echo` is not allowed in specifications, which never run."
  | Try _ when context.in_parallel ->
      report cursor Leaves_parallel (last_byte value.span)
        "`?` cannot leave a `parallel` block or a `parallel for`; return a `Result` from the \
         branch and use `?` after it."
  | Return _ when context.in_parallel ->
      report cursor Leaves_parallel value.span
        "`return` cannot leave a `parallel` block or a `parallel for`."
  | Break | Continue -> loop_exit cursor context value
  | _ -> ());
  match value.kind with
  | Lambda { body; _ } ->
      let loop = match context.loop with Outside -> Outside | _ -> Across_lambda in
      block cursor { context with assert_allowed = false; in_parallel = false; loop } body
  | _ -> parts cursor context value

and parts cursor context value =
  Syntax_walk.expression_parts ~expression:(expression cursor context)
    ~statement:(statement cursor context) value

and loop_exit cursor context (value : expression) =
  let word = match value.kind with Break -> "break" | _ -> "continue" in
  match (context.loop, value.kind) with
  | Inside, _ | Parallel_body, Continue -> ()
  | Outside, _ ->
      report cursor Misplaced_loop_exit value.span
        (Printf.sprintf "`%s` is only allowed in a loop." word)
  | Across_lambda, _ ->
      report cursor Misplaced_loop_exit value.span
        (Printf.sprintf "`%s` cannot reach a loop outside the lambda it is in." word)
  | Parallel_body, _ ->
      report cursor Leaves_parallel value.span
        "`break` cannot leave a `parallel for`; `continue` can."
  | Branch, _ ->
      report cursor Leaves_parallel value.span
        (Printf.sprintf "`%s` cannot leave a branch of a `parallel` block." word)

and block cursor context (body : block) = List.iter (statement cursor context) body.statements

and types ?(parameter = false) cursor context type_ =
  requires_placement cursor ~top:parameter type_;
  Syntax_walk.type_expression (expression cursor (specification context)) type_

(* A [requires] on a function type constrains the arguments a callee passes its callback,
   so it belongs only on the type of a definition's parameter, at its top:
   never on a field's, a result's, or a type argument's. *)
and requires_placement cursor ~top (type_ : type_expression) =
  match type_.kind with
  | Function_type { inputs; output; clauses; _ } ->
      if not top then
        List.iter
          (fun (clause : clause) ->
            match clause.kind with
            | Requires _ ->
                report cursor Misplaced_requires clause.span
                  "A function type has a `requires` only as the type of a parameter, where it \
                   constrains the arguments the callee passes its callback."
            | _ -> ())
          clauses;
      List.iter (fun (_, input) -> requires_placement cursor ~top:false input) inputs;
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
        | Parallel_loop -> { context with loop = Parallel_body; in_parallel = true }
        | Sequential -> { context with loop = Inside }
        | Concurrent_loop -> { context with loop = Inside }
      in
      block cursor body_context body
  | While { condition; clauses; body } ->
      expression cursor context condition;
      loop_clauses cursor context clauses;
      block cursor { context with loop = Inside } body
  | Parallel body ->
      let loop = match context.loop with Outside -> Outside | _ -> Branch in
      block cursor { context with in_parallel = true; loop } body
  | Concurrent body -> block cursor context body
  | Proof body ->
      if not context.function_body then
        report cursor Misplaced_proof statement.span
          "A `proof` block is only allowed in a function's body.";
      block cursor (proof context) body
  | Assert _ ->
      if not context.assert_allowed then
        report cursor Misplaced_assert statement.span
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
            report cursor Reserved_specification_name name.span
              "A parameter cannot be named `result`, which names the return value in `ensures` and \
               `cost`.";
          if lends && name.text = "final" then
            report cursor Reserved_specification_name name.span
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

let signature cursor (signature : signature) =
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
  Option.iter (block cursor { plain with function_body = true }) body

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
        (fun (member : trait_member line) ->
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
        (fun (member : impl_member line) ->
          match member.kind with
          | Associated_definition (_, type_) -> types cursor plain type_
          | Capability_definition _ | Impl_member_error -> ())
        members
  | Capability _ -> ()
  | Constant { type_; value; _ } ->
      types cursor plain type_;
      expression cursor plain value
  | Test { body; _ } -> block cursor { plain with assert_allowed = true } body
  | Theorem { generics; parameters = theorem_parameters; clauses = theorem_clauses; body; _ } ->
      generic_parameters cursor generics;
      parameters cursor theorem_parameters;
      clauses cursor theorem_clauses;
      block cursor (proof plain) body
  | Law_proof { type_; body; _ } ->
      generic_parameters cursor type_.generics;
      block cursor (proof plain) body
  | Definition_error _ -> ()

(* The rules that need the whole tree of one definition: where
   specification-only forms, [assert], [proof], [yield], [break],
   [continue], [return], [?], and [echo] may appear. See PARSER.md, "Checks
   on a whole definition".

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
  proof : bool;  (** Theorem bodies, [proof] blocks, and law proofs *)
  function_body : bool;  (** Where a [proof] block may appear *)
  yields : bool;  (** In a method whose signature [yields], outside lambdas *)
  loop : loop;
  parallel : bool;
      (** In a [parallel] branch or a [parallel for] body, where [return] and [?] cannot leave *)
}

let plain =
  {
    specification = false;
    assert_allowed = false;
    proof = false;
    function_body = false;
    yields = false;
    loop = Outside;
    parallel = false;
  }

let specification context = { context with specification = true }
let proof context = { context with specification = true; assert_allowed = true; proof = true }

let report cursor code (span : span) message =
  Cursor.report cursor code (Cursor.absolute cursor span) message

(* The last byte of a span, where the [?] of [x?] is. *)
let last_byte (span : span) = Syntax.Span.make (max span.start (span.stop - 1)) span.stop

let rec expression cursor context (value : expression) =
  (match value.kind with
  | Quantified { quantifier; _ } when not context.specification ->
      report cursor Specification_only value.span
        (Printf.sprintf
           "`%s` is only for specifications: `requires`, `ensures`, invariants, `decreases`, \
            `cost`, laws, theorems, and proofs"
           (match quantifier with Forall -> "forall" | Exists -> "exists"))
  | Binary (Implies, _, _) when not context.specification ->
      report cursor Specification_only value.span
        "`==>` is only for specifications; in code, write `!a || b`"
  | Echo _ when context.proof ->
      report cursor Echo_in_proof value.span "`echo` is not allowed in proofs"
  | Try _ when context.parallel ->
      report cursor Leaves_parallel (last_byte value.span)
        "`?` cannot leave a `parallel` block or a `parallel for`; return a `Result` from the \
         branch and use `?` after it"
  | Return _ when context.parallel ->
      report cursor Leaves_parallel value.span
        "`return` cannot leave a `parallel` block or a `parallel for`"
  | Break | Continue -> loop_exit cursor context value
  | _ -> ());
  match value.kind with
  | Lambda { body; _ } ->
      let loop = match context.loop with Outside -> Outside | _ -> Across_lambda in
      block cursor
        { context with assert_allowed = false; yields = false; parallel = false; loop }
        body
  | If { condition; then_; else_ } -> (
      expression cursor context condition;
      block cursor context then_;
      match else_ with
      | Some (Else body) -> block cursor context body
      | Some (Else_if value) -> expression cursor context value
      | None -> ())
  | Match { scrutinees; arms } ->
      List.iter (expression cursor context) scrutinees;
      List.iter
        (fun (arm : arm) ->
          Option.iter (expression cursor context) arm.guard;
          statement cursor context arm.body)
        arms
  | Provide { implementations; body } ->
      List.iter (expression cursor context) implementations;
      block cursor context body
  | Block body -> block cursor context body
  | _ -> Syntax_walk.children (expression cursor context) value

and loop_exit cursor context (value : expression) =
  let word = match value.kind with Break -> "break" | _ -> "continue" in
  match (context.loop, value.kind) with
  | Inside, _ | Parallel_body, Continue -> ()
  | Outside, _ ->
      report cursor Misplaced_loop_exit value.span
        (Printf.sprintf "`%s` is only allowed in a loop" word)
  | Across_lambda, _ ->
      report cursor Misplaced_loop_exit value.span
        (Printf.sprintf "`%s` cannot reach a loop outside the lambda it is in" word)
  | Parallel_body, _ ->
      report cursor Leaves_parallel value.span
        "`break` cannot leave a `parallel for`; `continue` can"
  | Branch, _ ->
      report cursor Leaves_parallel value.span
        (Printf.sprintf "`%s` cannot leave a branch of a `parallel` block" word)

and block cursor context (body : block) = List.iter (statement cursor context) body.statements

and types cursor context type_ =
  Syntax_walk.type_expression (expression cursor (specification context)) type_

and loop_clauses cursor context clauses =
  List.iter (Syntax_walk.loop_clause (expression cursor (specification context))) clauses

and statement cursor context (statement : statement) =
  match statement.kind with
  | Let { annotation; value; else_; _ } ->
      Option.iter (types cursor context) annotation;
      expression cursor context value;
      Option.iter (block cursor context) else_
  | Expression value -> expression cursor context value
  | Assignment { target; value; _ } ->
      expression cursor context target;
      expression cursor context value
  | For { parallel; iterable; clauses; body; _ } ->
      expression cursor context iterable;
      loop_clauses cursor context clauses;
      let body_context =
        if parallel then { context with loop = Parallel_body; parallel = true }
        else { context with loop = Inside }
      in
      block cursor body_context body
  | While { condition; clauses; body } ->
      expression cursor context condition;
      loop_clauses cursor context clauses;
      block cursor { context with loop = Inside } body
  | Parallel body ->
      let loop = match context.loop with Outside -> Outside | _ -> Branch in
      block cursor { context with parallel = true; loop } body
  | Proof body ->
      if not context.function_body then
        report cursor Misplaced_proof statement.span
          "a `proof` block is only allowed in a function's body";
      block cursor (proof context) body
  | Assert value ->
      if not context.assert_allowed then
        report cursor Misplaced_assert statement.span
          "`assert` is only allowed in tests, theorems, and proofs";
      expression cursor context value
  | Yield value ->
      if not context.yields then
        report cursor Misplaced_yield statement.span
          "`yield` is only allowed in a method whose signature `yields`";
      expression cursor context value
  | Statement_error -> ()

(* Definitions *)

let parameters cursor (parameters : parameter list) =
  List.iter
    (fun (parameter : parameter) ->
      match parameter.kind with
      | Named_parameter { name; type_; default; _ } ->
          if name.text = "result" then
            report cursor Reserved_name name.span
              "a parameter cannot be named `result`, which names the return value in `ensures` and \
               `cost`";
          types cursor plain type_;
          Option.iter (expression cursor plain) default
      | Self_parameter _ | Parameter_error -> ())
    parameters

let clauses cursor clauses =
  List.iter (Syntax_walk.clause (expression cursor (specification plain))) clauses

let generic_parameters cursor generics =
  List.iter (Syntax_walk.generic_parameter (expression cursor (specification plain))) generics

let signature cursor (signature : signature) =
  Syntax_walk.function_name (expression cursor (specification plain)) signature.name;
  generic_parameters cursor signature.generics;
  parameters cursor signature.parameters;
  (match signature.result with
  | Some (Returns type_ | Yields (_, type_)) -> types cursor plain type_
  | None -> ());
  clauses cursor signature.clauses

let function_definition cursor (definition : function_definition) =
  signature cursor definition.signature;
  let yields = match definition.signature.result with Some (Yields _) -> true | _ -> false in
  Option.iter (block cursor { plain with function_body = true; yields }) definition.body

let fields cursor (fields : field list) =
  List.iter
    (fun (field : field) ->
      types cursor plain field.type_;
      Option.iter (expression cursor plain) field.default)
    fields

let definition cursor (definition : definition) =
  match definition.kind with
  | Function function_ -> function_definition cursor function_
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
        (fun (member : trait_member member) ->
          match member.kind with
          | Trait_method function_ -> function_definition cursor function_
          | Law law ->
              parameters cursor law.parameters;
              List.iter (expression cursor (specification plain)) law.requires;
              block cursor (specification plain) law.body
          | Associated_type _ | Trait_member_error -> ())
        members
  | Impl { type_; members; _ } ->
      generic_parameters cursor type_.generics;
      List.iter
        (fun (member : impl_member member) ->
          match member.kind with
          | Impl_method function_ -> function_definition cursor function_
          | Associated_definition (_, type_) -> types cursor plain type_
          | Impl_member_error -> ())
        members
  | Capability { members; _ } ->
      List.iter
        (fun (member : capability_member member) ->
          match member.kind with
          | Capability_method method_ -> signature cursor method_
          | Capability_member_error -> ())
        members
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
      types cursor plain type_;
      block cursor (proof plain) body
  | Definition_error -> ()

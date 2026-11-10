(* Blocks and statements, with a block's lines, trailing lambdas, and loops.
   This module sets [Parse_hooks]. *)

open Syntax
open Atoms
open Parse_type
open Parse_expression

(* Before a [{] that must open a body, one line break is skipped, so a body
   can start on the line after a signature's clauses or a loop's header. *)
let rec opens_body cursor =
  Cursor.is_punctuation cursor (Open Curly)
  || (Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly))

and body_opening cursor =
  if Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) then
    Cursor.advance cursor;
  if not (Cursor.is_punctuation cursor (Open Curly)) then Cursor.fail cursor "`{` to start the body"

and body cursor =
  body_opening cursor;
  block cursor

and block cursor : block =
  let start = cursor.Cursor.index in
  let previous = ref None in
  let item cursor =
    let statement = statement_line cursor ~previous:!previous in
    previous := Some statement;
    statement
  in
  let statements =
    Cursor.lines cursor ~item ~recover:(fun start span ->
        previous := None;
        {
          kind = Statement_error;
          span;
          blank_line_before = Cursor.blank_line_before cursor start;
          id = Cursor.fresh cursor;
        })
  in
  { statements; span = Cursor.span_from cursor start; id = Cursor.fresh cursor }

(* A statement that is a line of a block. Habits from other languages that
   show up at the end of a statement, or as [elif] after an [if], are
   reported here. *)
and statement_line cursor ~previous : statement =
  match (Cursor.peek cursor, previous) with
  | ({ kind = Lower "elif"; _ } as elif_token), Some { kind = Expression { kind = If _; _ }; _ }
    when begins_expression (Cursor.peek_ahead cursor 1) ->
      let start = cursor.Cursor.index in
      Habits.elif cursor ~previous_stop:(Cursor.token_at cursor (start - 2)).span.stop ~elif_token;
      Cursor.advance cursor;
      let condition = expression cursor in
      let then_ = body cursor in
      let else_ =
        if Cursor.accept_keyword cursor Else then
          Some
            (if Cursor.is_keyword cursor If then Else_if (if_expression cursor)
             else Else (body cursor))
        else None
      in
      let value = expression_node cursor start (If { condition; then_; else_ }) in
      {
        kind = Expression value;
        span = value.span;
        blank_line_before = Cursor.blank_line_before cursor start;
        id = Cursor.fresh cursor;
      }
  | _ ->
      let statement = statement cursor in
      end_of_statement cursor statement

(* What may follow a statement on its line, where the grammar allows only a
   line break or [}]: habits are reported and parsing goes on. *)
and end_of_statement cursor (statement : statement) =
  match (Cursor.peek_kind cursor, statement.kind) with
  | Foreign (Plus_plus | Minus_minus), Expression target
    when match Cursor.peek_ahead cursor 1 with
         | Newline | End_of_file | Punctuation (Close _) -> true
         | _ -> false ->
      let operator = Cursor.next cursor in
      Habits.increment cursor ~target ~operator;
      let operator_kind =
        if operator.kind = Foreign Plus_plus then Add_assign else Subtract_assign
      in
      let one : expression =
        { kind = Integer Z.one; span = Cursor.span cursor operator.span; id = Cursor.fresh cursor }
      in
      let stop = (Cursor.span cursor operator.span).stop in
      {
        statement with
        kind = Assignment { target; operator = operator_kind; value = one };
        span = Syntax.Span.make statement.span.start stop;
      }
  | Punctuation (Open Curly), _ when not (Cursor.peek cursor).line_break_before ->
      trailing_lambda cursor statement
  | _ -> statement

(* The statement with the name or member it ends with, as [items.map] ends
   [let names = items.map], replaced by [replace] of it, or [None] when it
   ends with neither. The nodes around it are extended to where the
   replacement ends. *)
and replace_trailing (statement : statement) ~replace =
  let rec rightmost (value : expression) =
    let around kind (inner : expression) : expression =
      (* The same node, so it keeps its id, with its span reaching the replacement's end. *)
      { value with kind; span = Syntax.Span.make value.span.start inner.span.stop }
    in
    match value.kind with
    | Name _ | Member _ -> Some (replace value)
    | Binary binary ->
        Option.map
          (fun right -> around (Binary { binary with right }) right)
          (rightmost binary.right)
    | Return (Some inner) ->
        Option.map (fun inner -> around (Return (Some inner)) inner) (rightmost inner)
    | Echo inner -> Option.map (fun inner -> around (Echo inner) inner) (rightmost inner)
    | Mode (mode, inner) ->
        Option.map (fun inner -> around (Mode (mode, inner)) inner) (rightmost inner)
    | Any inner -> Option.map (fun inner -> around (Any inner) inner) (rightmost inner)
    | _ -> None
  in
  let rebuilt kind (value : expression) : statement =
    { statement with kind; span = Syntax.Span.make statement.span.start value.span.stop }
  in
  match statement.kind with
  | Expression value -> Option.map (fun value -> rebuilt (Expression value) value) (rightmost value)
  | Let binding ->
      Option.map (fun value -> rebuilt (Let { binding with value }) value) (rightmost binding.value)
  | Assignment assignment ->
      Option.map
        (fun value -> rebuilt (Assignment { assignment with value }) value)
        (rightmost assignment.value)
  | _ -> None

(* The [it] tokens of a block, including those in its interpolations. *)
and uses_of_it (tokens : Token.t array) =
  List.concat_map
    (fun (token : Token.t) ->
      match token.kind with
      | Lower "it" -> [ token ]
      | String literal ->
          List.concat_map
            (fun (inner : Token.interpolation) -> uses_of_it inner.tokens)
            (Array.to_list (Token.interpolations literal))
      | _ -> [])
    (Array.to_list tokens)

and rename_it (tokens : Token.t array) ~parameter =
  Array.map
    (fun (token : Token.t) ->
      match token.kind with
      | Lower "it" -> { token with kind = Lower parameter }
      | String literal ->
          let rest =
            Array.map
              (fun ((inner : Token.interpolation), text) ->
                ({ inner with tokens = rename_it inner.tokens ~parameter }, text))
              literal.rest
          in
          { token with kind = String { literal with rest } }
      | _ -> token)
    tokens

(* [items.map { it.name }]: a block on the same line after a call without
   parentheses, which uses [it]. It is parsed as the call the fix writes:
   the block becomes a lambda's body, with [it] renamed to the parameter. *)
and trailing_lambda cursor statement =
  let opening = Cursor.peek cursor in
  let closer = Cursor.closer cursor cursor.index in
  let closing = Cursor.token_at cursor closer in
  let block_tokens = Array.sub cursor.tokens cursor.index (closer - cursor.index + 1) in
  let uses = uses_of_it block_tokens in
  let replace (callee : expression) : expression =
    let parameter = Habits.parameter_name callee in
    Habits.trailing_lambda cursor ~callee ~parameter ~opening ~closing ~uses;
    let renamed = rename_it block_tokens ~parameter in
    let body = block (Cursor.over cursor renamed) in
    Cursor.skip_to cursor (closer + 1);
    let at_start = Syntax.Span.make body.span.start body.span.start in
    let lambda : expression =
      {
        kind =
          Lambda
            {
              parameters =
                [
                  {
                    kind =
                      Binding_or_constant
                        { text = parameter; span = at_start; id = Cursor.fresh cursor };
                    span = at_start;
                    id = Cursor.fresh cursor;
                  };
                ];
              body;
            };
        span = body.span;
        id = Cursor.fresh cursor;
      }
    in
    {
      kind = Call (callee, [ { label = None; value = lambda } ]);
      span = Syntax.Span.make callee.span.start body.span.stop;
      id = Cursor.fresh cursor;
    }
  in
  if uses = [] then statement
  else Option.value (replace_trailing statement ~replace) ~default:statement

and statement cursor : statement =
  let start = cursor.Cursor.index in
  let blank_line_before = Cursor.blank_line_before cursor start in
  let finish kind : statement =
    { kind; span = Cursor.span_from cursor start; blank_line_before; id = Cursor.fresh cursor }
  in
  match Cursor.peek_kind cursor with
  | Keyword Let ->
      let let_token = Cursor.next cursor in
      if Cursor.is_keyword cursor Mut then begin
        let mut_token = Cursor.next cursor in
        Habits.let_mut cursor ~let_token ~mut_token;
        finish (binding cursor ~mutable_:true)
      end
      else finish (binding cursor ~mutable_:false)
  | Keyword Var ->
      Cursor.advance cursor;
      finish (binding cursor ~mutable_:true)
  | Keyword For ->
      Cursor.advance cursor;
      finish (for_loop cursor ~mode:Sequential)
  | Keyword While ->
      Cursor.advance cursor;
      let condition = expression cursor in
      let clauses = loop_clauses cursor in
      finish (While { condition; clauses; body = body cursor })
  | Keyword Parallel ->
      Cursor.advance cursor;
      if Cursor.accept_keyword cursor For then finish (for_loop cursor ~mode:Parallel_loop)
      else finish (Parallel (body cursor))
  | Keyword Concurrent ->
      Cursor.advance cursor;
      if Cursor.accept_keyword cursor For then finish (for_loop cursor ~mode:Concurrent_loop)
      else finish (Concurrent (body cursor))
  | Keyword Proof ->
      Cursor.advance cursor;
      finish (Proof (body cursor))
  | Keyword Assert ->
      Cursor.advance cursor;
      finish (Assert (expression cursor))
  | Keyword Yield ->
      Cursor.advance cursor;
      finish (Yield (expression cursor))
  | Reserved Loop when Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) ->
      let loop_token = Cursor.next cursor in
      Habits.loop cursor ~loop_token;
      let condition = expression_node cursor start True in
      finish (While { condition; clauses = []; body = body cursor })
  | _ -> (
      let target = expression cursor in
      match assignment_operator (Cursor.peek_kind cursor) with
      | Some operator ->
          Cursor.advance cursor;
          finish (Assignment { target; operator; value = expression cursor })
      | None -> finish (Expression target))

(* After [let] or [var]. The expression before a [let ... else] cannot end
   with [}], so that the [else] cannot be read as part of it. *)
and binding cursor ~mutable_ =
  let pattern = Parse_pattern.pattern cursor in
  let annotation =
    if Cursor.accept_punctuation cursor Colon then Some (type_expression cursor) else None
  in
  Cursor.expect_punctuation cursor Equal;
  let value = expression cursor in
  let else_ =
    if Cursor.is_keyword cursor Else then begin
      let before = Cursor.token_at cursor (cursor.index - 1) in
      if before.kind = Punctuation (Close Curly) then begin
        let span = Cursor.absolute cursor value.span in
        Cursor.report cursor Let_else_brace (Cursor.peek cursor).span
          "The expression before the `else` of a `let ... else` cannot end with `}`; put it in \
           parentheses."
          ~fixes:
            [
              Diagnostic.fix "Put the expression in parentheses"
                [ Diagnostic.insert span.start "("; Diagnostic.insert span.stop ")" ];
            ]
      end;
      Cursor.advance cursor;
      Some (body cursor)
    end
    else None
  in
  Let { mutable_; pattern; annotation; value; else_ }

and for_loop cursor ~mode =
  let pattern = Parse_pattern.pattern cursor in
  Cursor.expect_keyword cursor In;
  let iterable = expression cursor in
  (* In [for i in 0.. {}], the grammar reads the body as the end of the
     range, and the loop then has no body: the mistake is the range. *)
  (match iterable.kind with
  | Range { stop = Some { kind = Block _; _ }; operator_span; _ } when not (opens_body cursor) ->
      Cursor.report cursor Open_range
        (Cursor.absolute cursor operator_span)
        (open_range_message "end");
      raise Cursor.Failed
  | _ -> ());
  let clauses = loop_clauses cursor in
  For { mode; pattern; iterable; clauses; body = body cursor }

(* [invariant] and [cost] may repeat; [decreases] appears at most once. *)
and loop_clauses cursor =
  let rec loop clauses =
    let start = cursor.Cursor.index in
    match Cursor.peek_kind cursor with
    | Keyword Cost ->
        let keyword = Cursor.next cursor in
        let cost = cost cursor in
        if cost.amortized || cost.bound = Finite then
          Cursor.report cursor Loop_cost_bound keyword.span
            (Printf.sprintf
               "A loop's `cost` states what the loop has spent so far, so it takes `O(...)`, `<=`, \
                or `==`%s. %s"
               (if cost.bound = Finite then "" else ", and is never `amortized`")
               (if cost.bound = Finite then
                  "A loop shows that it ends with `decreases`, not with `time finite`."
                else
                  "Potential belongs to the values the loop changes, which the function's own \
                   `cost` accounts for."));
        loop
          (({
              kind = Loop_cost cost;
              span = Cursor.span_from cursor start;
              id = Cursor.fresh cursor;
            }
             : loop_clause)
          :: clauses)
    | Keyword Invariant ->
        Cursor.advance cursor;
        let value = expression cursor in
        loop
          (({
              kind = Invariant value;
              span = Cursor.span_from cursor start;
              id = Cursor.fresh cursor;
            }
             : loop_clause)
          :: clauses)
    | Keyword Decreases ->
        let keyword = Cursor.next cursor in
        if
          List.exists
            (fun (clause : loop_clause) ->
              match clause.kind with Loop_decreases _ -> true | _ -> false)
            clauses
        then
          Cursor.report cursor Repeated_clause keyword.span
            "A loop has at most one `decreases` clause; list several measures in one, separated by \
             commas.";
        let measures = expression_list cursor in
        loop
          (({
              kind = Loop_decreases measures;
              span = Cursor.span_from cursor start;
              id = Cursor.fresh cursor;
            }
             : loop_clause)
          :: clauses)
    | _ -> List.rev clauses
  in
  loop []

let () =
  Parse_hooks.expression_hook := Parse_expression.expression;
  Parse_hooks.block_hook := block;
  Parse_hooks.body_hook := body;
  Parse_hooks.body_opening_hook := body_opening;
  Parse_hooks.statement_hook := statement

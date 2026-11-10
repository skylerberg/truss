(* Expressions.

   Types, clauses, expressions, and statements contain each other: a
   statement has a type annotation, a type in parentheses can carry a [cost]
   clause, and a clause holds expressions. They are parsed by
   [Parse_type], this module, and [Parse_statement], in that order; an
   earlier one reaches a later one through [Parse_hooks]. Patterns contain
   none of them, and are their own module.

   Expressions are parsed with a total order of precedence. The combinations
   Truss's partial order leaves out are reported afterward by [Operators],
   which can quote both operands in its fixes. *)

open Token
open Syntax
open Atoms
open Parse_hooks
open Parse_type

(* The operators of the total order, loosest first. The levels Truss defines
   are its own; the order among the shift and bitwise levels, which Truss
   leaves undefined, is Rust's. *)
type operator = Binary_operator of binary | Is_operator | Range_operator of bool

let implies_level = 0
let or_level = 1
let and_level = 2
let comparison_level = 3
let range_level = 4

let operator = function
  | Punctuation Implies -> Some (Binary_operator Implies, implies_level)
  | Punctuation Or_or -> Some (Binary_operator Or, or_level)
  | Punctuation And_and -> Some (Binary_operator And, and_level)
  | Punctuation Equal_equal -> Some (Binary_operator Equal, comparison_level)
  | Punctuation Not_equal -> Some (Binary_operator Not_equal, comparison_level)
  | Punctuation Less -> Some (Binary_operator Less, comparison_level)
  | Punctuation Less_equal -> Some (Binary_operator Less_equal, comparison_level)
  | Punctuation Greater -> Some (Binary_operator Greater, comparison_level)
  | Punctuation Greater_equal -> Some (Binary_operator Greater_equal, comparison_level)
  | Keyword Is -> Some (Is_operator, comparison_level)
  | Punctuation Dot_dot -> Some (Range_operator false, range_level)
  | Punctuation Dot_dot_equal -> Some (Range_operator true, range_level)
  | Punctuation Bar -> Some (Binary_operator Bit_or, 5)
  | Punctuation Caret -> Some (Binary_operator Bit_xor, 6)
  | Punctuation Ampersand -> Some (Binary_operator Bit_and, 7)
  | Punctuation Shift_left -> Some (Binary_operator Shift_left, 8)
  | Punctuation Shift_right -> Some (Binary_operator Shift_right, 8)
  | Punctuation Plus -> Some (Binary_operator Add, 9)
  | Punctuation Minus -> Some (Binary_operator Subtract, 9)
  | Punctuation Star -> Some (Binary_operator Multiply, 10)
  | Punctuation Slash -> Some (Binary_operator Divide, 10)
  | Punctuation Percent -> Some (Binary_operator Remainder, 10)
  | _ -> None

let assignment_operator = function
  | Punctuation Equal -> Some Assign
  | Punctuation Plus_equal -> Some Add_assign
  | Punctuation Minus_equal -> Some Subtract_assign
  | Punctuation Star_equal -> Some Multiply_assign
  | Punctuation Slash_equal -> Some Divide_assign
  | Punctuation Percent_equal -> Some Remainder_assign
  | Punctuation Ampersand_equal -> Some Bit_and_assign
  | Punctuation Bar_equal -> Some Bit_or_assign
  | Punctuation Caret_equal -> Some Bit_xor_assign
  | Punctuation Shift_left_equal -> Some Shift_left_assign
  | Punctuation Shift_right_equal -> Some Shift_right_assign
  | _ -> None

(* An expression at the lowest level. Inside brackets, [open_range] lets a
   range leave out its start or its end. *)
let rec expression ?(open_range = false) cursor =
  Cursor.nested cursor (fun cursor ->
      let start = cursor.Cursor.index in
      let value = binary cursor ~level:0 ~open_range in
      match Cursor.peek cursor with
      | { kind = Punctuation Question; _ } as question -> (
          match conditional_follows (Cursor.peek_ahead cursor 1) with
          | true ->
              Cursor.advance cursor;
              conditional cursor start value question
          | false -> value)
      | _ -> value)

and binary cursor ~level ~open_range =
  let start = cursor.Cursor.index in
  let left =
    match Cursor.peek_kind cursor with
    | Punctuation ((Dot_dot | Dot_dot_equal) as range) when level <= range_level ->
        let token = Cursor.next cursor in
        if not open_range then open_range_error cursor token "start";
        let stop = range_stop cursor ~open_range in
        expression_node cursor start
          (Range
             {
               start = None;
               operator_span = Cursor.span cursor token.span;
               stop;
               inclusive = range = Dot_dot_equal;
             })
    | _ -> prefix cursor
  in
  let rec loop (left : expression) =
    match operator (Cursor.peek_kind cursor) with
    | Some (operator, operator_level) when operator_level >= level -> (
        let operator_span = Cursor.span cursor (Cursor.next cursor).span in
        match operator with
        | Binary_operator operator ->
            let right = binary cursor ~level:(operator_level + 1) ~open_range:false in
            loop (expression_node cursor start (Binary { operator; operator_span; left; right }))
        | Is_operator ->
            let pattern = Parse_pattern.pattern cursor in
            loop (expression_node cursor start (Is { value = left; operator_span; pattern }))
        | Range_operator inclusive ->
            let stop = range_stop cursor ~open_range in
            loop
              (expression_node cursor start
                 (Range { start = Some left; operator_span; stop; inclusive })))
    | _ -> left
  in
  loop left

(* The end of a range after [..] or [..=], which only brackets let a range
   leave out. *)
and range_stop cursor ~open_range =
  match Cursor.peek_kind cursor with
  | Punctuation (Close Square | Comma) when open_range -> None
  | kind when begins_expression kind ->
      Some (binary cursor ~level:(range_level + 1) ~open_range:false)
  | _ ->
      open_range_error cursor (Cursor.token_at cursor (cursor.index - 1)) "end";
      None

and open_range_message part =
  Printf.sprintf "A range without a%s %s is only allowed directly in brackets, as in `items[2..]`."
    (if part = "end" then "n" else "")
    part

and open_range_error cursor (token : Token.t) part =
  Cursor.report cursor Open_range token.span (open_range_message part);
  raise Cursor.Failed

and prefix cursor : expression =
  let start = cursor.Cursor.index in
  let value =
    match Cursor.peek_kind cursor with
    | Punctuation Minus -> prefix_operator cursor start Negate
    | Punctuation Bang -> prefix_operator cursor start Not
    | Punctuation Tilde -> prefix_operator cursor start Complement
    | Keyword Mut ->
        Cursor.advance cursor;
        expression_node cursor start (Mode (Mut, postfix cursor))
    | Keyword Own ->
        Cursor.advance cursor;
        expression_node cursor start (Mode (Own, postfix cursor))
    | Keyword Any ->
        Cursor.advance cursor;
        expression_node cursor start (Any (postfix cursor))
    | Keyword (Forall | Exists) -> quantified cursor
    | Keyword Echo ->
        Cursor.advance cursor;
        expression_node cursor start (Echo (expression cursor))
    | Keyword Return ->
        Cursor.advance cursor;
        let value =
          if begins_expression (Cursor.peek_kind cursor) then Some (expression cursor) else None
        in
        expression_node cursor start (Return value)
    | Foreign Minus_minus ->
        let operator = Cursor.next cursor in
        let operand = Cursor.nested cursor prefix in
        Habits.double_negation cursor ~operator ~operand;
        let inner = expression_node cursor (start + 1) (Prefix (Negate, operand)) in
        expression_node cursor start (Prefix (Negate, inner))
    | Punctuation Ampersand ->
        let before =
          if start > cursor.first then Some (Cursor.token_at cursor (start - 1)) else None
        in
        let ampersand = Cursor.next cursor in
        Habits.address_of cursor ~before ~ampersand ~next:(Cursor.peek cursor);
        prefix cursor
    | Punctuation (Bar | Or_or) -> closure_bars cursor
    | _ -> postfix cursor
  in
  match Cursor.peek_kind cursor with
  (* [x as Int64], with the type on the same line as [as]. *)
  | Reserved As when not (Cursor.token_at cursor (cursor.index + 1)).line_break_before ->
      let as_token = Cursor.next cursor in
      let target = type_expression cursor in
      Habits.as_conversion cursor ~value ~as_token ~target;
      (* Parsed as the call it means, [Int64.from(x)]. *)
      let callee : expression_kind =
        match target.kind with
        | Path_type { path; arguments = []; _ } ->
            Member
              ( { kind = Name path; span = target.span; id = Cursor.fresh cursor },
                { text = "from"; span = target.span; id = Cursor.fresh cursor } )
        | _ -> Expression_error
      in
      expression_node cursor start
        (Call
           ( { kind = callee; span = target.span; id = Cursor.fresh cursor },
             [ { label = None; value } ] ))
  | _ -> value

and prefix_operator cursor start operator =
  Cursor.advance cursor;
  let operand = Cursor.nested cursor prefix in
  expression_node cursor start (Prefix (operator, operand))

(* [forall index in 0..count => body], whose body runs to the end of the
   expression. *)
and quantified cursor =
  let start = cursor.Cursor.index in
  let quantifier = if (Cursor.next cursor).kind = Keyword Forall then Forall else Exists in
  let binder =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, Punctuation Colon ->
        let name = Atoms.name cursor (Cursor.next cursor) text in
        Cursor.advance cursor;
        Binder_type (name, type_expression cursor)
    | _ ->
        let pattern = Parse_pattern.pattern cursor in
        Cursor.expect_keyword cursor In;
        Binder_in (pattern, expression cursor)
  in
  Cursor.expect_punctuation cursor Fat_arrow;
  expression_node cursor start (Quantified { quantifier; binder; body = expression cursor })

(* [|x| x + 1], from Rust: reported, and parsed as the lambda it means. *)
and closure_bars cursor =
  let start = cursor.Cursor.index in
  let opening = Cursor.next cursor in
  let parameters, closing =
    if opening.kind = Punctuation Or_or then ([], opening)
    else
      let rec loop parameters =
        if Cursor.is_punctuation cursor Bar then (List.rev parameters, Cursor.next cursor)
        else
          let parameter = Parse_pattern.primary cursor in
          if not (Cursor.is_punctuation cursor Bar) then Cursor.expect_punctuation cursor Comma;
          loop (parameter :: parameters)
      in
      loop []
  in
  let body_start = cursor.index in
  let body = expression cursor in
  Habits.closure_bars cursor ~opening ~closing ~body ~before_else:(Cursor.is_keyword cursor Else);
  let block =
    match body.kind with
    | Block block -> block
    | _ ->
        let statement : statement =
          {
            kind = Expression body;
            span = body.span;
            blank_line_before = false;
            id = Cursor.fresh cursor;
          }
        in
        {
          statements = [ statement ];
          span = Cursor.span_from cursor body_start;
          id = Cursor.fresh cursor;
        }
  in
  expression_node cursor start (Lambda { parameters; body = block })

and postfix cursor : expression =
  let start = cursor.Cursor.index in
  let rec loop (value : expression) =
    match Cursor.peek_kind cursor with
    | Punctuation Dot -> (
        Cursor.advance cursor;
        match Cursor.peek_kind cursor with
        | Lower text | Upper text ->
            let name = Atoms.name cursor (Cursor.next cursor) text in
            loop (expression_node cursor start (Member (value, name)))
        | _ -> Cursor.fail cursor "a name after `.`")
    | Punctuation (Open Square) ->
        let items =
          Cursor.bracketed cursor ~item:bracket_item ~recover:(fun span ->
              Item { kind = Expression_error; span; id = Cursor.fresh cursor })
        in
        if items = [] then begin
          (* At the [\]], so that one the lexer inserted reports nothing. *)
          cursor.index <- cursor.index - 1;
          Cursor.fail cursor "an index or type arguments"
        end;
        (* A range that leaves out an end must be alone in its brackets. *)
        if List.compare_length_with items 1 > 0 then
          List.iter
            (function
              | Item
                  {
                    kind =
                      ( Range { start = None; operator_span; _ }
                      | Range { stop = None; operator_span; _ } );
                    _;
                  } ->
                  Cursor.report cursor Open_range
                    (Cursor.absolute cursor operator_span)
                    "A range without a start or an end must be the only item in its brackets, as \
                     in `items[2..]`."
              | _ -> ())
            items;
        loop (expression_node cursor start (Bracket (value, items)))
    | Punctuation (Open Paren) ->
        let arguments = arguments cursor in
        loop (expression_node cursor start (Call (value, arguments)))
    (* A [?] that starts [x ? a : b] is left for [expression], whose whole
       left side is the condition, as in the languages it comes from. *)
    | Punctuation Question when not (conditional_follows (Cursor.peek_ahead cursor 1)) ->
        Cursor.advance cursor;
        loop (expression_node cursor start (Try value))
    | Keyword With ->
        Cursor.advance cursor;
        if not (Cursor.is_punctuation cursor (Open Paren)) then
          Cursor.fail cursor "`(` after `with`";
        let updates =
          Cursor.bracketed cursor ~item:update ~recover:(fun span ->
              { kind = Update_error; span; id = Cursor.fresh cursor })
        in
        loop (expression_node cursor start (With (value, updates)))
    | _ -> value
  in
  loop (primary cursor)

(* Whether the token after a [?] starts the second part of [x ? a : b]: a
   token that can start an expression but cannot follow a [?] in Truss. *)
and conditional_follows = function
  | Punctuation (Open _ | Minus | Dot_dot | Dot_dot_equal) -> false
  | kind -> begins_expression kind

and conditional cursor start condition question =
  let then_ = expression cursor in
  Cursor.expect_punctuation cursor Colon;
  let else_ = expression cursor in
  Habits.conditional cursor ~condition ~then_ ~else_ ~question;
  let block (value : expression) : block =
    {
      statements =
        [
          {
            kind = Expression value;
            span = value.span;
            blank_line_before = false;
            id = Cursor.fresh cursor;
          };
        ];
      span = value.span;
      id = Cursor.fresh cursor;
    }
  in
  expression_node cursor start
    (If { condition; then_ = block then_; else_ = Some (Else (block else_)) })

and bracket_item cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper text, Punctuation Equal ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      Item_constraint (name, type_expression cursor)
  | _ -> Item (expression cursor ~open_range:true)

and arguments cursor =
  Cursor.bracketed cursor ~item:argument ~recover:(fun span ->
      { label = None; value = { kind = Expression_error; span; id = Cursor.fresh cursor } })

and argument cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Lower text, Punctuation Colon ->
      let label = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      { label = Some label; value = expression cursor }
  | _ -> { label = None; value = expression cursor }

(* [server.port: 443], or a bare [x]. *)
and update cursor : update =
  let start = cursor.Cursor.index in
  let field = Atoms.lower cursor "a field name" in
  let rec path fields =
    if Cursor.accept_punctuation cursor Dot then path (Atoms.lower cursor "a field name" :: fields)
    else List.rev fields
  in
  let path = path [] in
  let value = if Cursor.accept_punctuation cursor Colon then Some (expression cursor) else None in
  {
    kind = Update { field; path; value };
    span = Cursor.span_from cursor start;
    id = Cursor.fresh cursor;
  }

and primary cursor : expression =
  let start = cursor.Cursor.index in
  let simple kind =
    Cursor.advance cursor;
    expression_node cursor start kind
  in
  match Cursor.peek_kind cursor with
  | Integer value -> simple (Integer value)
  | Float value -> simple (Float value)
  | String literal ->
      expression_node cursor start (String (string_literal cursor ~start ~modules:[] literal))
  | Keyword True -> simple True
  | Keyword False -> simple False
  | Keyword Todo -> simple Todo
  | Keyword Unreachable -> simple Unreachable
  | Keyword Break -> simple Break
  | Keyword Continue -> simple Continue
  | Keyword Self_value -> simple Self_value
  | Keyword Self_type -> simple Self_type_value
  | Lower _ | Upper _ -> named cursor start
  | Punctuation (Open Paren) -> (
      let closer = Cursor.closer cursor start in
      Cursor.advance cursor;
      match
        let inner = expression cursor in
        if cursor.index < closer then Cursor.fail cursor "`)`";
        inner
      with
      | inner ->
          Cursor.skip_to cursor (closer + 1);
          expression_node cursor start (Parenthesized inner)
      | exception Cursor.Failed ->
          Cursor.skip_to cursor (closer + 1);
          error_expression cursor start)
  | Punctuation (Open Square) -> collection cursor
  | Punctuation (Open Curly) -> expression_node cursor start (Block (block cursor))
  | Keyword Fn -> lambda cursor
  | Keyword If -> if_expression cursor
  | Keyword Match -> match_expression cursor
  | Keyword Provide ->
      Cursor.advance cursor;
      let implementations = expression_list cursor in
      expression_node cursor start (Provide { implementations; body = body cursor })
  | _ -> Cursor.fail cursor "an expression"

(* A primary that starts with a name: [items], [json::parse], [Point],
   [geometry::Shape], or a tagged string after its module. *)
and named cursor start =
  let modules = Atoms.module_prefix cursor in
  match Cursor.peek_kind cursor with
  | Lower text ->
      expression_node cursor start
        (Name { modules; last = Atoms.name cursor (Cursor.next cursor) text })
  | Upper text ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      let value = expression_node cursor start (Name { modules; last = name }) in
      if brace_record_follows cursor then brace_record cursor start value else value
  | String ({ tag = Some _; _ } as literal) ->
      expression_node cursor start (String (string_literal cursor ~start ~modules literal))
  | Punctuation Less -> (
      (* The last module is the function. *)
      match List.rev modules with
      | last :: reversed -> turbofish cursor start { modules = List.rev reversed; last }
      | [] -> Cursor.fail cursor "a name")
  | _ -> Cursor.fail cursor "a name after `::`"

(* [Point { x: 1.0 }] on one line: a [{] that starts with a label can never
   open a block. *)
and brace_record_follows cursor =
  let opening = Cursor.peek cursor in
  opening.kind = Punctuation (Open Curly)
  && (not opening.line_break_before)
  &&
  match (Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Lower _, Punctuation Colon -> true
  | _ -> false

and brace_record cursor start (record : expression) =
  let opening = Cursor.peek cursor in
  let closer = Cursor.closer cursor cursor.index in
  Cursor.advance cursor;
  let first = Cursor.peek cursor in
  let rec loop arguments =
    if cursor.index >= closer then List.rev arguments
    else
      let argument = argument cursor in
      if cursor.index < closer then Cursor.expect_punctuation cursor Comma;
      loop (argument :: arguments)
  in
  let arguments = loop [] in
  let last_stop = Cursor.previous_stop cursor in
  let closing = Cursor.token_at cursor closer in
  Cursor.skip_to cursor (closer + 1);
  Habits.brace_record cursor ~name_stop:(Cursor.absolute cursor record.span).stop ~opening ~first
    ~last_stop ~closing;
  expression_node cursor start (Call (record, arguments))

(* [parse::<Int64>(text)], from Rust. The last module is the function. *)
and turbofish cursor start (function_path : path) =
  let less = Cursor.next cursor in
  let colons = Cursor.token_at cursor (cursor.index - 2) in
  let rec loop types =
    let types = type_expression cursor :: types in
    if Cursor.accept_punctuation cursor Comma then loop types else List.rev types
  in
  let types = loop [] in
  if not (Cursor.is_punctuation cursor Greater) then
    Cursor.fail cursor "`>` after the type arguments";
  let greater = Cursor.next cursor in
  Habits.turbofish cursor ~colons ~less ~greater;
  (* Parsed as it is written in Truss, where type arguments in an
     expression are expressions: [parse[Int64]]. *)
  let rec as_expression (type_ : type_expression) : expression =
    match type_.kind with
    | Path_type { path; arguments = []; _ } ->
        { kind = Name path; span = type_.span; id = Cursor.fresh cursor }
    | Path_type { path; arguments; span } ->
        let items =
          List.map
            (function
              | Type_argument argument -> Item (as_expression argument)
              | Count (value, span) -> Item { kind = Integer value; span; id = Cursor.fresh cursor }
              | Count_name name ->
                  Item
                    {
                      kind = Name { modules = []; last = name };
                      span = name.span;
                      id = Cursor.fresh cursor;
                    }
              | Constraint (name, argument) -> Item_constraint (name, argument))
            arguments
        in
        {
          kind =
            Bracket ({ kind = Name path; span = path.last.span; id = Cursor.fresh cursor }, items);
          span;
          id = Cursor.fresh cursor;
        }
    | _ -> { kind = Expression_error; span = type_.span; id = Cursor.fresh cursor }
  in
  let definition_name = expression_node cursor start (Name function_path) in
  expression_node cursor start
    (Bracket (definition_name, List.map (fun type_ -> Item (as_expression type_)) types))

and string_literal cursor ~start ~modules literal =
  Atoms.string_literal cursor ~start ~modules literal ~interpolation:(interpolation cursor)

(* An interpolation is parsed from its own token array, with the same base,
   so its spans are relative to the definition too. *)
and interpolation cursor (inner : Token.interpolation) : expression =
  (* The interpolation's tokens end with its End_of_file. *)
  let stop = Array.length inner.tokens - 1 in
  let nested = Cursor.over cursor inner.tokens ~stop in
  (* A closed interpolation's span ends with its [}]; one a line break cut
     off ends without it, and the lexer already reported it. *)
  let written = Cursor.text cursor inner.span in
  nested.cut_off_end <- written = "" || written.[String.length written - 1] <> '}';
  (* An empty interpolation, or one a line break cut off before its first
     token, already has the lexer's error. *)
  if stop = 0 then
    { kind = Expression_error; span = Cursor.span cursor inner.span; id = Cursor.fresh cursor }
  else
    match
      let value = expression nested in
      if not (Cursor.at_end nested) then Cursor.fail nested "the end of the interpolation";
      value
    with
    | value -> value
    | exception Cursor.Failed ->
        { kind = Expression_error; span = Cursor.span cursor inner.span; id = Cursor.fresh cursor }

(* [[1, 2]], [[]], [["a": 1]], and [[:]]. A map is told from a list by the
   [:] after its first element. *)
and collection cursor =
  let start = cursor.Cursor.index in
  match (Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Punctuation Colon, Punctuation (Close Square) ->
      Cursor.advance cursor;
      Cursor.advance cursor;
      Cursor.advance cursor;
      expression_node cursor start (Map [])
  | _ -> (
      (* Each element is parsed as a key with an optional value, and then
         they must agree: all values, a map, or none, a list. *)
      let element cursor =
        let key = expression cursor in
        let value =
          if Cursor.accept_punctuation cursor Colon then Some (expression cursor) else None
        in
        (key, value)
      in
      let elements =
        Cursor.bracketed cursor ~item:element ~recover:(fun span ->
            ({ kind = Expression_error; span; id = Cursor.fresh cursor }, None))
      in
      let is_error ((key : expression), _) = key.kind = Expression_error in
      let entries =
        List.filter_map (fun (key, value) -> Option.map (fun value -> (key, value)) value) elements
      in
      match elements with
      | first :: _ when (not (is_error first)) && snd first <> None ->
          if List.length entries = List.length elements then
            expression_node cursor start (Map entries)
          else mixed_collection cursor start (List.find (fun (_, value) -> value = None) elements)
      | _ -> (
          match List.find_opt (fun (_, value) -> value <> None) elements with
          | None -> expression_node cursor start (List (List.map fst elements))
          | Some entry -> mixed_collection cursor start entry))

(* A collection whose elements mix list elements with map entries. *)
and mixed_collection cursor start ((key : expression), _) =
  Cursor.report cursor Unexpected_token (Cursor.absolute cursor key.span)
    "A collection holds either list elements or map entries, `key: value`, not both.";
  error_expression cursor start

and lambda cursor =
  let start = cursor.Cursor.index in
  Cursor.advance cursor;
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` after `fn` in a lambda";
  let parameters =
    Cursor.bracketed cursor ~item:Parse_pattern.pattern ~recover:(fun span ->
        { kind = Pattern_error; span; id = Cursor.fresh cursor })
  in
  expression_node cursor start (Lambda { parameters; body = body cursor })

and if_expression cursor =
  let start = cursor.Cursor.index in
  Cursor.expect_keyword cursor If;
  let condition = expression cursor in
  let then_ = body cursor in
  let else_ =
    if Cursor.accept_keyword cursor Else then
      Some
        (if Cursor.is_keyword cursor If then Else_if (if_expression cursor) else Else (body cursor))
    else None
  in
  expression_node cursor start (If { condition; then_; else_ })

and match_expression cursor =
  let start = cursor.Cursor.index in
  Cursor.advance cursor;
  let scrutinees = expression_list cursor in
  body_opening cursor;
  let arms =
    Cursor.lines cursor ~item:arm ~recover:(fun start span ->
        {
          patterns = [];
          guard = None;
          body =
            { kind = Statement_error; span; blank_line_before = false; id = Cursor.fresh cursor };
          span;
          blank_line_before = Cursor.blank_line_before cursor start;
          id = Cursor.fresh cursor;
        })
  in
  expression_node cursor start (Match { scrutinees; arms })

(* [Some(x), Tick if elapsed > limit => body]. *)
and arm cursor : arm =
  let start = cursor.Cursor.index in
  let rec patterns list =
    let list = Parse_pattern.pattern cursor :: list in
    if Cursor.accept_punctuation cursor Comma then patterns list else List.rev list
  in
  let patterns = patterns [] in
  let guard = if Cursor.accept_keyword cursor If then Some (expression cursor) else None in
  Cursor.expect_punctuation cursor Fat_arrow;
  let body = statement cursor in
  (match Cursor.peek cursor with
  | { kind = Punctuation Comma; _ } as comma ->
      Habits.match_arm_comma cursor ~comma;
      Cursor.advance cursor;
      cursor.line_ended <- true
  | _ -> ());
  {
    patterns;
    guard;
    body;
    span = Cursor.span_from cursor start;
    blank_line_before = Cursor.blank_line_before cursor start;
    id = Cursor.fresh cursor;
  }

(* Types, clauses, expressions, and statements.

   These contain each other: a statement has a type annotation, a function
   type in parentheses carries [cost] and [requires] clauses, a clause holds
   expressions, and an expression holds blocks of statements. They are
   therefore one group of mutually recursive functions. Patterns contain
   none of them, and are their own module.

   Expressions are parsed with a total order of precedence. The
   combinations that Truss's partial order excludes are reported after
   parsing, so that a fix can quote both operands. *)

open Token
open Syntax
open Atoms

let is_clause_keyword = function
  | Keyword (Uses | Requires | Ensures | Decreases | Cost) -> true
  | _ -> false

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

(* The index of the [>] or [>>] that closes the [<] at the cursor, or [None]
   when the tokens after the [<] are not type arguments or generic
   parameters closed on the same line. A [>>] closes two [<]. *)
let angle_closer cursor =
  let rec scan index depth =
    match (Cursor.token_at cursor index).kind with
    | Punctuation Less -> scan (index + 1) (depth + 1)
    | Punctuation Greater -> if depth = 1 then Some index else scan (index + 1) (depth - 1)
    | Punctuation Shift_right ->
        if depth = 2 then Some index else if depth > 2 then scan (index + 1) (depth - 2) else None
    | Punctuation (Open _) ->
        let closer = Cursor.closer cursor index in
        if closer < 0 then None else scan (closer + 1) depth
    | Upper _ | Lower _ | Integer _
    | Punctuation (Comma | Colon | Colon_colon | Dot | Equal | Plus | Arrow)
    | Keyword (Self_type | Any | Fn | Mut | Own | Capability) ->
        scan (index + 1) depth
    | _ -> None
  in
  scan cursor.Cursor.index 0

(* [List<String>] and [fn first<T>]: angle brackets where type arguments or
   generic parameters go, from Rust, Java, and TypeScript. The cursor is at
   the [<]. The tokens up to its closer are parsed by [parse] as the square
   brackets that the fix writes, or the result is [None] when nothing closes
   the [<]. Tokens inside a nested bracket are left as they are, since a
   function type's [requires] there may compare with [<]. *)
let angle_brackets cursor parse =
  match angle_closer cursor with
  | None -> None
  | Some closer ->
      let rewritten = Dynarray.create () and angles = ref [] in
      let rec copy index =
        if index <= closer then begin
          let token = Cursor.token_at cursor index in
          let bracket kind (span : Source.span) =
            Dynarray.add_last rewritten { token with kind = Punctuation kind; span }
          in
          match token.kind with
          | Punctuation Less ->
              angles := token :: !angles;
              bracket (Open Square) token.span;
              copy (index + 1)
          | Punctuation Greater ->
              angles := token :: !angles;
              bracket (Close Square) token.span;
              copy (index + 1)
          | Punctuation Shift_right ->
              angles := token :: !angles;
              let middle = token.span.start + 1 in
              bracket (Close Square) (Source.span token.span.start middle);
              bracket (Close Square) (Source.span middle token.span.stop);
              copy (index + 1)
          | Punctuation (Open _) ->
              let nested_closer = Cursor.closer cursor index in
              for nested = index to nested_closer do
                Dynarray.add_last rewritten (Cursor.token_at cursor nested)
              done;
              copy (nested_closer + 1)
          | _ ->
              Dynarray.add_last rewritten token;
              copy (index + 1)
        end
      in
      copy cursor.index;
      Habits.angle_brackets cursor ~angles:(List.rev !angles);
      let value = parse (Cursor.sub_cursor cursor (Dynarray.to_array rewritten)) in
      Cursor.skip_to cursor (closer + 1);
      Some value

(* Whether a token of another language's macro call follows the name that
   stops at [name_stop]: a [!] and then a [(] or a [[], with no space
   between them, as in [println!(...)] and [vec![...]]. *)
let macro_follows cursor ~name_stop =
  let bang = Cursor.peek cursor and opener = Cursor.token_at cursor (cursor.Cursor.index + 1) in
  bang.kind = Punctuation Bang && bang.span.start = name_stop
  && opener.span.start = bang.span.stop
  && match opener.kind with Punctuation (Open (Paren | Square)) -> true | _ -> false

(* Whether [a ?? b] or [a ?: b] follows: a [?], then a [?] or a [:] with no
   space between them, then the start of an expression. Two forms that are
   valid Truss are excluded. [a?? - 1] and [a??(b)] apply [?] twice, so the
   token after [??] is not one that can continue an expression. A map
   entry whose key ends with [?], as in [[key?: value]], has no space
   before its [?], so [?:] needs one. *)
let coalescing_follows cursor =
  let question = Cursor.peek cursor and second = Cursor.token_at cursor (cursor.Cursor.index + 1) in
  let third = Cursor.peek_ahead cursor 2 in
  question.kind = Punctuation Question
  && second.span.start = question.span.stop
  && begins_expression third
  &&
  match second.kind with
  | Punctuation Question -> (
      match third with Punctuation (Open _ | Minus | Dot_dot | Dot_dot_equal) -> false | _ -> true)
  | Punctuation Colon -> question.span.start > Cursor.previous_stop cursor
  | _ -> false

(* Whether a comma separates items directly inside the bracket whose opener
   is at [opener], as in a tuple, [(a, b)]. *)
let has_comma cursor ~opener =
  let closer = Cursor.closer cursor opener in
  let rec scan index =
    index < closer
    &&
    match (Cursor.token_at cursor index).kind with
    | Punctuation Comma -> true
    | Punctuation (Open _) -> scan (Cursor.closer cursor index + 1)
    | _ -> scan (index + 1)
  in
  scan (opener + 1)

let rec type_expression cursor : type_expression = Cursor.nested cursor type_expression_in

and type_expression_in cursor : type_expression =
  let start = cursor.Cursor.index in
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Keyword Self_type, _, _ ->
      Cursor.advance cursor;
      let associated =
        if Cursor.accept_punctuation cursor Dot then
          Some (Atoms.upper cursor "an associated type after `Self.`")
        else None
      in
      type_node cursor start (Self_type associated)
  | Keyword Any, _, _ ->
      Cursor.advance cursor;
      type_node cursor start (Any_type (path_type cursor))
  | Keyword Fn, _, _ -> type_node cursor start (Function_type (function_type cursor ~clauses:false))
  | Punctuation (Open Paren), _, _ -> parenthesized_function_type cursor
  | Upper text, Punctuation Dot, Upper _ ->
      let parameter = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      type_node cursor start (Associated (parameter, Atoms.upper cursor "an associated type"))
  | (Upper _ | Lower _), _, _ -> type_node cursor start (Path_type (path_type cursor))
  | _ -> Cursor.fail cursor "a type"

(* [geometry::Shape], [List[String]], [Array[UInt8, 32]]. *)
and path_type cursor : path_type =
  let start = cursor.Cursor.index in
  let path = Atoms.upper_path cursor "a type name" in
  let arguments =
    if Cursor.is_punctuation cursor (Open Square) then type_arguments cursor
    else if Cursor.is_punctuation cursor Less then
      Option.value (angle_brackets cursor type_arguments) ~default:[]
    else []
  in
  { path; arguments; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

and type_arguments cursor =
  let start = cursor.Cursor.index in
  let arguments =
    Cursor.bracketed cursor ~item:type_argument ~recover:(fun span ->
        Type_argument { kind = Type_error; span; id = Cursor.fresh_id cursor })
  in
  if arguments = [] then begin
    Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
      "Type arguments cannot be empty.";
    raise Cursor.Failed
  end;
  arguments

and type_argument cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Integer value, _ ->
      let token = Cursor.next cursor in
      Count (value, Cursor.span cursor token.span)
  | Lower text, next when next <> Punctuation Colon_colon ->
      Count_name (Atoms.name cursor (Cursor.next cursor) text)
  | Upper text, Punctuation Equal ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      Cursor.advance cursor;
      Constraint (name, type_expression cursor)
  | _ -> Type_argument (type_expression cursor)

(* [fn(Element, Element) -> Ordering], with [uses], [cost], and [requires]
   clauses only when it is in parentheses. Its inputs are named, as in
   [fn(element: Element)], exactly when it has a [requires], which names
   them. *)
and function_type cursor ~clauses:with_clauses =
  let start = cursor.Cursor.index in
  Cursor.expect_keyword cursor Fn;
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` after `fn` in a function type";
  let inputs =
    Cursor.bracketed cursor
      ~item:(fun cursor ->
        let name =
          match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
          | Lower text, Punctuation Colon ->
              let name = Atoms.name cursor (Cursor.next cursor) text in
              Cursor.advance cursor;
              Some name
          | _ -> None
        in
        let mode = mode cursor in
        (name, (mode, type_expression cursor)))
      ~recover:(fun span ->
        (None, (None, { kind = Type_error; span; id = Cursor.fresh_id cursor })))
  in
  let output =
    if Cursor.accept_punctuation cursor Arrow then Some (type_expression cursor) else None
  in
  let clauses =
    if with_clauses then
      let rec loop clauses =
        match Cursor.peek_kind cursor with
        | Keyword (Uses | Cost | Requires) -> loop (clause cursor :: clauses)
        | Keyword (Ensures | Decreases) ->
            Cursor.fail cursor
              "`uses`, `cost`, or `requires`; a function type has no `ensures` or `decreases`"
        | _ -> List.rev clauses
      in
      loop []
    else []
  in
  let names = List.filter_map fst inputs in
  let requires =
    List.exists (fun (clause : clause) -> match clause.kind with Requires _ -> true | _ -> false)
  in
  let span = (Cursor.token_at cursor start).span in
  if requires clauses then
    begin if List.length names <> List.length inputs then
      Cursor.report cursor Function_type_names span
        "A function type with `requires` names every input, as in `fn(index: USize)`, so that the \
         `requires` can mention them."
    end
  else if names <> [] then
    Cursor.report cursor Function_type_names span
      "A function type names its inputs only when a `requires` mentions them; remove the names, \
       since calls through a function value pass arguments by position.";
  {
    inputs = List.map snd inputs;
    input_names = (if List.length names = List.length inputs then names else []);
    output;
    clauses;
  }

and parenthesized_function_type cursor =
  let start = cursor.Cursor.index in
  let closer = Cursor.closer cursor start in
  Cursor.advance cursor;
  match
    if (not (Cursor.is_keyword cursor Fn)) && has_comma cursor ~opener:start then
      Habits.tuple cursor ~opening:(Cursor.token_at cursor start);
    if not (Cursor.is_keyword cursor Fn) then
      Cursor.fail cursor
        "a function type; parentheses in a type only hold a function type with clauses";
    let function_type = function_type cursor ~clauses:true in
    if function_type.clauses = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
        "Parentheses around a function type are only for its clauses; remove them.";
      raise Cursor.Failed
    end;
    if cursor.index < closer then Cursor.fail cursor "`)` after the clauses of the function type";
    function_type
  with
  | function_type ->
      Cursor.skip_to cursor (closer + 1);
      type_node cursor start (Function_type function_type)
  | exception Cursor.Failed ->
      Cursor.skip_to cursor (closer + 1);
      type_node cursor start Type_error

(* [Element: Hash + Ordered]: one or more path types joined by [+]. *)
and bounds cursor =
  let rec loop bounds =
    let bounds = path_type cursor :: bounds in
    if Cursor.accept_punctuation cursor Plus then loop bounds else List.rev bounds
  in
  loop []

and generics cursor : generic_parameter list =
  if Cursor.is_punctuation cursor Less then
    Option.value (angle_brackets cursor generics) ~default:[]
  else if not (Cursor.is_punctuation cursor (Open Square)) then []
  else
    let start = cursor.Cursor.index in
    let parameters =
      Cursor.bracketed cursor ~item:generic_parameter ~recover:(fun span ->
          { kind = Generic_error; span; id = Cursor.fresh_id cursor })
    in
    if parameters = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.token_at cursor start).span
        "Generic parameters cannot be empty.";
      raise Cursor.Failed
    end;
    parameters

and generic_parameter cursor : generic_parameter =
  let start = cursor.Cursor.index in
  let kind =
    match Cursor.peek_kind cursor with
    | Keyword Capability ->
        Cursor.advance cursor;
        Capability_parameter (Atoms.upper cursor "the name of a capability parameter")
    | Upper text ->
        let name = Atoms.name cursor (Cursor.next cursor) text in
        Type_parameter (name, if Cursor.accept_punctuation cursor Colon then bounds cursor else [])
    | Lower text ->
        let name = Atoms.name cursor (Cursor.next cursor) text in
        Cursor.expect_punctuation cursor Colon;
        Value_parameter (name, type_expression cursor)
    | _ -> Cursor.fail cursor "a generic parameter"
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

(* [Equal, Hash]. *)
and path_type_list cursor =
  let rec loop paths =
    let paths = path_type cursor :: paths in
    if Cursor.accept_punctuation cursor Comma then loop paths else List.rev paths
  in
  loop []

(* [FileRead], [Self.Uses], [Source.Uses]. *)
and capability_reference cursor : capability_reference =
  let start = cursor.Cursor.index in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
    | Keyword Self_type, _, _ ->
        Cursor.advance cursor;
        if not (Cursor.accept_punctuation cursor Dot) then
          Cursor.fail cursor
            "`.` and an associated capability set, as in `Self.Uses`; `Self` is a type, not a \
             capability";
        Self_capabilities (Atoms.upper cursor "an associated capability set after `Self.`")
    | Upper text, Punctuation Dot, Upper _ ->
        let parameter = Atoms.name cursor (Cursor.next cursor) text in
        Cursor.advance cursor;
        Associated_capabilities (parameter, Atoms.upper cursor "an associated capability set")
    | _ -> Capability_path (path_type cursor)
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

(* [FileRead, FileWrite]. *)
and capability_list cursor =
  let rec loop capabilities =
    let capabilities = capability_reference cursor :: capabilities in
    if Cursor.accept_punctuation cursor Comma then loop capabilities else List.rev capabilities
  in
  loop []

and expression_list cursor =
  let rec loop expressions =
    let expressions = expression cursor :: expressions in
    if Cursor.accept_punctuation cursor Comma then loop expressions else List.rev expressions
  in
  loop []

(* One clause of a signature; the current token is its keyword. *)
and clause cursor : clause =
  let start = cursor.Cursor.index in
  let keyword = Cursor.next cursor in
  let kind =
    match keyword.kind with
    | Keyword Uses -> Uses (capability_list cursor)
    | Keyword Requires -> Requires (expression cursor)
    | Keyword Ensures -> Ensures (expression cursor)
    | Keyword Decreases -> Decreases (expression_list cursor)
    | Keyword Cost -> Cost (cost cursor)
    | _ -> Cursor.fail cursor "a clause"
  in
  { kind; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

(* [cost [amortized] resource bound], after [cost]. A type's
   [cost potential expression] is parsed with the type. *)
and cost cursor =
  let amortized =
    match (Cost_word.of_token (Cursor.peek_kind cursor), Cursor.peek_ahead cursor 1) with
    | Some Amortized, Lower _ ->
        Cursor.advance cursor;
        true
    | _ -> false
  in
  if Cost_word.of_token (Cursor.peek_kind cursor) = Some Potential then begin
    Cursor.report cursor Misplaced_potential (Cursor.peek cursor).span
      "`cost potential` belongs to a type, and states the potential its values hold.";
    raise Cursor.Failed
  end;
  let resource =
    match
      Cost_word.expect cursor ~accepted:Cost_word.resources ~category:"a resource"
        ~expected:"a resource: `time`, `allocations`, `allocated_bytes`, or `calls(...)`"
    with
    | Time -> Time
    | Allocations -> Allocations
    | Allocated_bytes -> Allocated_bytes
    | _ -> Calls (call_target cursor)
  in
  let bound_token = Cursor.peek cursor in
  let bound =
    match bound_token.kind with
    | Punctuation Less_equal ->
        Cursor.advance cursor;
        At_most (expression cursor)
    | Punctuation Equal_equal ->
        Cursor.advance cursor;
        Exactly (expression cursor)
    | _ -> (
        (* [finite] is a bound only for [time], so it is suggested only
           there. *)
        let suggested = if resource = Time then [ Cost_word.O; Finite ] else [ O ] in
        match
          Cost_word.expect cursor ~accepted:[ O; Finite ] ~suggested ~category:"a bound"
            ~expected:"a bound: `O(...)`, `finite`, `<=`, or `==`"
        with
        | O -> Big_o (parenthesized_expression cursor)
        | _ ->
            if resource <> Time then
              Cursor.report cursor Finite_not_time bound_token.span
                "`finite` is a bound only for `time`; a countable resource takes `O(...)`, `<=`, \
                 or `==`.";
            Finite)
  in
  { amortized; resource; bound }

(* The target of [calls(...)]: a parameter, a capability, or one of its
   methods. *)
and call_target cursor =
  let opener = cursor.Cursor.index in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(` after `calls`";
  let closer = Cursor.closer cursor opener in
  Cursor.advance cursor;
  let target =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower text, next when next <> Punctuation Colon_colon ->
        Call_parameter (Atoms.name cursor (Cursor.next cursor) text)
    | _ ->
        let capability = path_type cursor in
        if Cursor.accept_punctuation cursor Dot then
          Call_method (capability, Atoms.lower cursor "a method name")
        else Call_capability capability
  in
  if cursor.index < closer then Cursor.fail cursor "`)` after the target of `calls`";
  Cursor.skip_to cursor (closer + 1);
  target

(* An expression in parentheses that are part of the enclosing construct,
   as in [O(...)]. *)
and parenthesized_expression cursor =
  let opener = cursor.Cursor.index in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(`";
  let closer = Cursor.closer cursor opener in
  Cursor.advance cursor;
  let value = expression cursor in
  if cursor.index < closer then Cursor.fail cursor "`)`";
  Cursor.skip_to cursor (closer + 1);
  value

(* An expression at the lowest level. Inside brackets, [open_range] lets a
   range leave out its start or its end. *)
and expression ?(open_range = false) cursor =
  Cursor.nested cursor (fun cursor ->
      let start = cursor.Cursor.index in
      let value = pipes cursor start (binary cursor ~level:0 ~open_range) in
      match Cursor.peek cursor with
      | { kind = Punctuation Question; _ } when coalescing_follows cursor ->
          coalescing cursor start value
      | { kind = Punctuation Question; _ } as question -> (
          match conditional_follows (Cursor.peek_ahead cursor 1) with
          | true ->
              Cursor.advance cursor;
              conditional cursor start value question
          | false -> value)
      | _ -> value)

(* [value |> function], from Elixir, F#, and OCaml: reported, and parsed as
   the call [function(value)]. *)
and pipes cursor start (value : expression) =
  match Cursor.peek cursor with
  | { kind = Foreign Pipe_greater; _ } as operator ->
      Cursor.advance cursor;
      let callee = binary cursor ~level:0 ~open_range:false in
      Habits.pipe_operator cursor ~value ~operator ~callee;
      pipes cursor start (expression_node cursor start (Call (callee, [ { label = None; value } ])))
  | _ -> value

(* [a ?? b] and [a ?: b], from C#, JavaScript, Swift, and Kotlin: reported,
   and parsed as the call [a.unwrap_or(b)]. *)
and coalescing cursor start (value : expression) =
  let first = Cursor.next cursor in
  let second = Cursor.next cursor in
  let default = binary cursor ~level:0 ~open_range:false in
  Habits.null_coalescing cursor ~value ~first ~second ~default;
  let method_ : name =
    { text = "unwrap_or"; span = Cursor.span cursor first.span; id = Cursor.fresh_id cursor }
  in
  let callee = expression_node cursor start (Member (value, method_)) in
  expression_node cursor start (Call (callee, [ { label = None; value = default } ]))

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
  let rec loop ~length (left : expression) =
    match operator (Cursor.peek_kind cursor) with
    | Some (operator, operator_level) when operator_level >= level -> (
        Cursor.check_chain_length cursor ~length;
        let loop = loop ~length:(length + 1) in
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
    | _ -> (
        match Cursor.peek cursor with
        (* [a ** b], from Python and JavaScript: reported, and parsed as a
           multiplication, so that both operands are checked. *)
        | { kind = Foreign Star_star; _ } as power ->
            Cursor.check_chain_length cursor ~length;
            Habits.power_operator cursor ~operator:power;
            Cursor.advance cursor;
            let right = prefix cursor in
            loop ~length:(length + 1)
              (expression_node cursor start
                 (Binary
                    {
                      operator = Multiply;
                      operator_span = Cursor.span cursor power.span;
                      left;
                      right;
                    }))
        | _ -> left)
  in
  loop ~length:0 left

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
        Cursor.nested cursor prefix
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
              ( { kind = Name path; span = target.span; id = Cursor.fresh_id cursor },
                { text = "from"; span = target.span; id = Cursor.fresh_id cursor } )
        | _ -> Expression_error
      in
      expression_node cursor start
        (Call
           ( { kind = callee; span = target.span; id = Cursor.fresh_id cursor },
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
            id = Cursor.fresh_id cursor;
          }
        in
        {
          statements = [ statement ];
          span = Cursor.span_from cursor body_start;
          id = Cursor.fresh_id cursor;
        }
  in
  expression_node cursor start (Lambda { parameters; body = block })

and postfix cursor : expression =
  let start = cursor.Cursor.index in
  let rec loop ~length (value : expression) =
    let loop value =
      Cursor.check_chain_length cursor ~length;
      loop ~length:(length + 1) value
    in
    match Cursor.peek_kind cursor with
    | Punctuation Dot -> (
        Cursor.advance cursor;
        match Cursor.peek_kind cursor with
        | Lower text | Upper text ->
            let name = Atoms.name cursor (Cursor.next cursor) text in
            loop (expression_node cursor start (Member (value, name)))
        | Integer _ | Float _ -> Habits.tuple_field cursor ~field:(Cursor.peek cursor)
        | _ -> Cursor.fail cursor "a name after `.`")
    | Punctuation (Open Square) ->
        let items =
          Cursor.bracketed cursor ~item:bracket_item ~recover:(fun span ->
              Item { kind = Expression_error; span; id = Cursor.fresh_id cursor })
        in
        if items = [] then begin
          (* The error is at the [\]], so that a [\]] the lexer inserted is not reported. *)
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
    (* A [?] that starts [x ? a : b] is left for [expression], because the
       condition is the whole expression before the [?], as in C and
       JavaScript. *)
    | Punctuation Question when coalescing_follows cursor -> value
    | Punctuation Question when not (conditional_follows (Cursor.peek_ahead cursor 1)) ->
        Cursor.advance cursor;
        loop (expression_node cursor start (Try value))
    | Keyword With ->
        Cursor.advance cursor;
        if not (Cursor.is_punctuation cursor (Open Paren)) then
          Cursor.fail cursor "`(` after `with`";
        let updates =
          Cursor.bracketed cursor ~item:update ~recover:(fun span ->
              { kind = Update_error; span; id = Cursor.fresh_id cursor })
        in
        loop (expression_node cursor start (With (value, updates)))
    | _ -> value
  in
  loop ~length:0 (primary cursor)

(* Whether the token after a [?] starts the second operand of
   [x ? a : b]: a token that can start an expression but cannot follow a
   [?] in Truss. *)
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
            id = Cursor.fresh_id cursor;
          };
        ];
      span = value.span;
      id = Cursor.fresh_id cursor;
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
      { label = None; value = { kind = Expression_error; span; id = Cursor.fresh_id cursor } })

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
    id = Cursor.fresh_id cursor;
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
  | Keyword Todo -> keyword_macro cursor (simple Todo)
  | Keyword Unreachable -> keyword_macro cursor (simple Unreachable)
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
        if Cursor.is_punctuation cursor Comma then
          Habits.tuple cursor ~opening:(Cursor.token_at cursor start);
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
      let token = Cursor.next cursor in
      let name = Atoms.name cursor token text in
      if modules = [] && macro_follows cursor ~name_stop:token.span.stop then
        macro cursor start name
      else expression_node cursor start (Name { modules; last = name })
  | Upper text ->
      let name = Atoms.name cursor (Cursor.next cursor) text in
      let value =
        path_separators cursor start (expression_node cursor start (Name { modules; last = name }))
      in
      let value = path_separators cursor start (angle_arguments cursor start value) in
      if brace_record_follows cursor then brace_record cursor start value else value
  | String ({ tag = Some _; _ } as literal) ->
      expression_node cursor start (String (string_literal cursor ~start ~modules literal))
  | Punctuation Less -> (
      (* The last module is the function. *)
      match List.rev modules with
      | last :: reversed -> turbofish cursor start { modules = List.rev reversed; last }
      | [] -> Cursor.fail cursor "a name")
  | _ -> Cursor.fail cursor "a name after `::`"

(* [Shape::Circle] and [Vec::new], from Rust and C++: each [::] after an
   uppercase name is reported, and parsed as the [.] that the fix writes. *)
and path_separators cursor start (value : expression) =
  match (Cursor.peek cursor, Cursor.peek_ahead cursor 1) with
  | ({ kind = Punctuation Colon_colon; _ } as separator), (Upper text | Lower text) ->
      Habits.path_separator cursor ~separator;
      Cursor.advance cursor;
      let name = Atoms.name cursor (Cursor.next cursor) text in
      path_separators cursor start (expression_node cursor start (Member (value, name)))
  | _ -> value

(* [List<String>.new()]: angle brackets after an uppercase name in an
   expression. A [<] there may be a comparison, so the brackets are type
   arguments only when a [.], a [(], or a [::] follows their closer. *)
and angle_arguments cursor start (value : expression) =
  let follows_closer closer =
    match (Cursor.token_at cursor (closer + 1)).kind with
    | Punctuation (Dot | Open Paren | Colon_colon) -> true
    | _ -> false
  in
  match if Cursor.is_punctuation cursor Less then angle_closer cursor else None with
  | Some closer when follows_closer closer -> (
      let items inner =
        Cursor.bracketed inner ~item:bracket_item ~recover:(fun span ->
            Item { kind = Expression_error; span; id = Cursor.fresh_id cursor })
      in
      match angle_brackets cursor items with
      | Some items -> expression_node cursor start (Bracket (value, items))
      | None -> value)
  | _ -> value

(* [println!(...)] and [vec![...]], from Rust: reported, and parsed as a
   call of the name, or as the list that [vec!] builds. *)
and macro cursor start (name : name) =
  let bang = Cursor.next cursor in
  let opening = Cursor.peek cursor in
  Habits.macro_call cursor ~name ~bang ~opening;
  match opening.kind with
  | Punctuation (Open Square) -> collection cursor
  | _ ->
      let callee = expression_node cursor start (Name { modules = []; last = name }) in
      let arguments = arguments cursor in
      expression_node cursor start (Call (callee, arguments))

(* [todo!()] and [unreachable!()], from Rust, after the keyword [value]:
   the [!] and its parentheses are reported and skipped. *)
and keyword_macro cursor (value : expression) =
  if macro_follows cursor ~name_stop:(Cursor.previous_stop cursor) then begin
    let bang = Cursor.next cursor in
    let closer = Cursor.closer cursor cursor.index in
    Habits.keyword_macro cursor ~bang ~closing:(Cursor.token_at cursor closer)
      ~empty:(closer = cursor.index + 1);
    Cursor.skip_to cursor (closer + 1)
  end;
  value

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
  (* Parsed as the Truss form [parse[Int64]], where type arguments in an
     expression are expressions. *)
  let rec as_expression (type_ : type_expression) : expression =
    match type_.kind with
    | Path_type { path; arguments = []; _ } ->
        { kind = Name path; span = type_.span; id = Cursor.fresh_id cursor }
    | Path_type { path; arguments; span; _ } ->
        let items =
          List.map
            (function
              | Type_argument argument -> Item (as_expression argument)
              | Count (value, span) ->
                  Item { kind = Integer value; span; id = Cursor.fresh_id cursor }
              | Count_name name ->
                  Item
                    {
                      kind = Name { modules = []; last = name };
                      span = name.span;
                      id = Cursor.fresh_id cursor;
                    }
              | Constraint (name, argument) -> Item_constraint (name, argument))
            arguments
        in
        {
          kind =
            Bracket ({ kind = Name path; span = path.last.span; id = Cursor.fresh_id cursor }, items);
          span;
          id = Cursor.fresh_id cursor;
        }
    | _ -> { kind = Expression_error; span = type_.span; id = Cursor.fresh_id cursor }
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
  let nested = Cursor.sub_cursor cursor inner.tokens ~stop in
  (* A closed interpolation's span ends with its [}]. The span of one that
     a line break ended does not, and the lexer already reported it. *)
  let source_text = Cursor.text cursor inner.span in
  nested.unterminated <- source_text = "" || source_text.[String.length source_text - 1] <> '}';
  (* An empty interpolation, or one that a line break ended before its
     first token, already has the lexer's error. *)
  if stop = 0 then
    { kind = Expression_error; span = Cursor.span cursor inner.span; id = Cursor.fresh_id cursor }
  else
    match
      let value = expression nested in
      if not (Cursor.at_end nested) then Cursor.fail nested "the end of the interpolation";
      value
    with
    | value -> value
    | exception Cursor.Failed ->
        {
          kind = Expression_error;
          span = Cursor.span cursor inner.span;
          id = Cursor.fresh_id cursor;
        }

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
            ({ kind = Expression_error; span; id = Cursor.fresh_id cursor }, None))
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
  (* A parameter's type and the result's type, as other languages write
     them, are reported and left out of the tree. *)
  let parameter cursor =
    let pattern = Parse_pattern.pattern cursor in
    if Cursor.is_punctuation cursor Colon then begin
      let from = Cursor.previous_stop cursor in
      Cursor.advance cursor;
      ignore (mode cursor);
      ignore (type_expression cursor);
      Habits.lambda_annotation cursor ~from ~stop:(Cursor.previous_stop cursor)
    end;
    pattern
  in
  let parameters =
    Cursor.bracketed cursor ~item:parameter ~recover:(fun span ->
        { kind = Pattern_error; span; id = Cursor.fresh_id cursor })
  in
  if Cursor.is_punctuation cursor Arrow then begin
    let from = Cursor.previous_stop cursor in
    Cursor.advance cursor;
    ignore (type_expression cursor);
    Habits.lambda_annotation cursor ~from ~stop:(Cursor.previous_stop cursor)
  end;
  expression_node cursor start (Lambda { parameters; body = body cursor })

(* [length] is the number of [else if] branches before this [if]. *)
and if_expression ?(length = 0) cursor =
  let start = cursor.Cursor.index in
  Cursor.expect_keyword cursor If;
  let condition = expression cursor in
  let then_ = body cursor in
  expression_node cursor start (If { condition; then_; else_ = else_branch cursor ~length })

and else_branch cursor ~length =
  if Cursor.accept_keyword cursor Else then
    if Cursor.is_keyword cursor If then begin
      Cursor.check_chain_length cursor ~length;
      Some (Else_if (if_expression cursor ~length:(length + 1)))
    end
    else Some (Else (body cursor))
  else None

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
            { kind = Statement_error; span; blank_line_before = false; id = Cursor.fresh_id cursor };
          span;
          blank_line_before = Cursor.blank_line_before cursor start;
          id = Cursor.fresh_id cursor;
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
    id = Cursor.fresh_id cursor;
  }

(* Before a [{] that must open a body, one line break is skipped, so a body
   can start on the line after a signature's clauses or a loop's header. *)
and opens_body cursor =
  Cursor.is_punctuation cursor (Open Curly)
  || (Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly))

and body_opening cursor =
  if Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) then
    Cursor.advance cursor;
  if not (Cursor.is_punctuation cursor (Open Curly)) then Cursor.fail cursor "`{` to start the body"

and body cursor =
  body_opening cursor;
  block cursor

and block cursor : block = Cursor.nested cursor block_in

and block_in cursor : block =
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
          id = Cursor.fresh_id cursor;
        })
  in
  { statements; span = Cursor.span_from cursor start; id = Cursor.fresh_id cursor }

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
      let else_ = else_branch cursor ~length:0 in
      let value = expression_node cursor start (If { condition; then_; else_ }) in
      {
        kind = Expression value;
        span = value.span;
        blank_line_before = Cursor.blank_line_before cursor start;
        id = Cursor.fresh_id cursor;
      }
  | _ ->
      let statement = statement cursor in
      end_of_statement cursor statement

(* The tokens that may follow a statement on its line, where the grammar allows only a
   line break or [}]: habits are reported and parsing continues. *)
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
        {
          kind = Integer Z.one;
          span = Cursor.span cursor operator.span;
          id = Cursor.fresh_id cursor;
        }
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

(* [statement] with its rightmost operand replaced by [replace] of that
   operand, when the operand is a name or a member, as [items.map] is in
   [let names = items.map]; otherwise [None]. The span of each enclosing
   node is extended to the end of the replacement. *)
and replace_trailing (statement : statement) ~replace =
  let rec rightmost (value : expression) =
    let with_operand kind (inner : expression) : expression =
      (* The same node, with the same id, and a span that ends where the replacement ends. *)
      { value with kind; span = Syntax.Span.make value.span.start inner.span.stop }
    in
    match value.kind with
    | Name _ | Member _ -> Some (replace value)
    | Binary binary ->
        Option.map
          (fun right -> with_operand (Binary { binary with right }) right)
          (rightmost binary.right)
    | Return (Some inner) ->
        Option.map (fun inner -> with_operand (Return (Some inner)) inner) (rightmost inner)
    | Echo inner -> Option.map (fun inner -> with_operand (Echo inner) inner) (rightmost inner)
    | Mode (mode, inner) ->
        Option.map (fun inner -> with_operand (Mode (mode, inner)) inner) (rightmost inner)
    | Any inner -> Option.map (fun inner -> with_operand (Any inner) inner) (rightmost inner)
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

(* [items.map { it.name }]: a block that uses [it], on the same line after
   a callee with no parentheses. It is parsed as the call the fix writes:
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
    let body = block (Cursor.sub_cursor cursor renamed) in
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
                        { text = parameter; span = at_start; id = Cursor.fresh_id cursor };
                    span = at_start;
                    id = Cursor.fresh_id cursor;
                  };
                ];
              body;
            };
        span = body.span;
        id = Cursor.fresh_id cursor;
      }
    in
    {
      kind = Call (callee, [ { label = None; value = lambda } ]);
      span = Syntax.Span.make callee.span.start body.span.stop;
      id = Cursor.fresh_id cursor;
    }
  in
  if uses = [] then statement
  else Option.value (replace_trailing statement ~replace) ~default:statement

and statement cursor : statement =
  let start = cursor.Cursor.index in
  let blank_line_before = Cursor.blank_line_before cursor start in
  let finish kind : statement =
    { kind; span = Cursor.span_from cursor start; blank_line_before; id = Cursor.fresh_id cursor }
  in
  match Cursor.peek_kind cursor with
  | Keyword Let ->
      let let_token = Cursor.next cursor in
      if Cursor.is_keyword cursor Mut then begin
        let mut_token = Cursor.next cursor in
        Habits.let_mut cursor ~let_token ~mut_token;
        finish (binding cursor ~is_var:true)
      end
      else finish (binding cursor ~is_var:false)
  | Keyword Var ->
      Cursor.advance cursor;
      finish (binding cursor ~is_var:true)
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
      let value = expression cursor in
      let by_bit_vector =
        match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
        | Lower "by", Lower "bit_vector" ->
            Cursor.advance cursor;
            Cursor.advance cursor;
            true
        | _ -> false
      in
      finish (Assert { value; by_bit_vector })
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
      match (assignment_operator (Cursor.peek_kind cursor), Cursor.peek cursor) with
      | Some operator, _ ->
          Cursor.advance cursor;
          finish (Assignment { target; operator; value = expression cursor })
      (* [name := value], from Go: reported, and parsed as the [let] it
         means. With any other target it is parsed as an assignment. *)
      | None, ({ kind = Foreign Colon_equal; _ } as operator) -> (
          Cursor.advance cursor;
          Habits.short_declaration cursor ~target ~operator;
          let value = expression cursor in
          match target.kind with
          | Name { modules = []; last } ->
              let pattern : pattern =
                { kind = Binding_or_constant last; span = target.span; id = Cursor.fresh_id cursor }
              in
              finish (Let { is_var = false; pattern; annotation = None; value; else_ = None })
          | _ -> finish (Assignment { target; operator = Assign; value }))
      | None, _ -> finish (Expression target))

(* After [let] or [var]. The expression before a [let ... else] cannot end
   with [}], so that the [else] cannot be read as part of it. *)
and binding cursor ~is_var =
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
                [
                  Diagnostic.insert (Source.zero_width span.start) "(";
                  Diagnostic.insert (Source.zero_width span.stop) ")";
                ];
            ]
      end;
      Cursor.advance cursor;
      Some (body cursor)
    end
    else None
  in
  Let { is_var; pattern; annotation; value; else_ }

and for_loop cursor ~mode =
  let pattern = Parse_pattern.pattern cursor in
  let annotation =
    if Cursor.accept_punctuation cursor Colon then Some (type_expression cursor) else None
  in
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
  For { mode; pattern; annotation; iterable; clauses; body = body cursor }

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
               "A loop's `cost` bounds the loop's cost so far, so it takes `O(...)`, `<=`, or \
                `==`%s. %s"
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
              id = Cursor.fresh_id cursor;
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
              id = Cursor.fresh_id cursor;
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
              id = Cursor.fresh_id cursor;
            }
             : loop_clause)
          :: clauses)
    | _ -> List.rev clauses
  in
  loop []

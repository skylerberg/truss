let is_clause_keyword = function
  | Token.Keyword (Uses | Requires | Ensures | Decreases | Cost) -> true
  | _ -> false

type operator = Binary_operator of Syntax.binary | Is_operator | Range_operator of bool

let comparison_level = 3
let range_level = 4

let rank_binary = function
  | Syntax.Connective Implies -> 0
  | Connective Or -> 1
  | Connective And -> 2
  | Comparison _ -> comparison_level
  | Operation (Bitwise Bit_or) -> 5
  | Operation (Bitwise Bit_xor) -> 6
  | Operation (Bitwise Bit_and) -> 7
  | Operation (Shift _) -> 8
  | Operation (Arithmetic (Add | Subtract)) -> 9
  | Operation (Arithmetic (Multiply | Divide | Remainder)) -> 10

let rank_operator = function
  | Binary_operator binary -> rank_binary binary
  | Is_operator -> comparison_level
  | Range_operator _ -> range_level

let find_operator = function
  | Token.Punctuation Implies -> Some (Binary_operator (Connective Implies))
  | Punctuation Or_or -> Some (Binary_operator (Connective Or))
  | Punctuation And_and -> Some (Binary_operator (Connective And))
  | Punctuation Equal_equal -> Some (Binary_operator (Comparison Equal))
  | Punctuation Not_equal -> Some (Binary_operator (Comparison Not_equal))
  | Punctuation Less -> Some (Binary_operator (Comparison Less))
  | Punctuation Less_equal -> Some (Binary_operator (Comparison Less_equal))
  | Punctuation Greater -> Some (Binary_operator (Comparison Greater))
  | Punctuation Greater_equal -> Some (Binary_operator (Comparison Greater_equal))
  | Keyword Is -> Some Is_operator
  | Punctuation Dot_dot -> Some (Range_operator false)
  | Punctuation Dot_dot_equal -> Some (Range_operator true)
  | Punctuation Bar -> Some (Binary_operator (Operation (Bitwise Bit_or)))
  | Punctuation Caret -> Some (Binary_operator (Operation (Bitwise Bit_xor)))
  | Punctuation Ampersand -> Some (Binary_operator (Operation (Bitwise Bit_and)))
  | Punctuation Shift_left -> Some (Binary_operator (Operation (Shift Shift_left)))
  | Punctuation Shift_right -> Some (Binary_operator (Operation (Shift Shift_right)))
  | Punctuation Plus -> Some (Binary_operator (Operation (Arithmetic Add)))
  | Punctuation Minus -> Some (Binary_operator (Operation (Arithmetic Subtract)))
  | Punctuation Star -> Some (Binary_operator (Operation (Arithmetic Multiply)))
  | Punctuation Slash -> Some (Binary_operator (Operation (Arithmetic Divide)))
  | Punctuation Percent -> Some (Binary_operator (Operation (Arithmetic Remainder)))
  | _ -> None

let find_assignment_operator = function
  | Token.Punctuation Equal -> Some Syntax.Assign
  | Punctuation Plus_equal -> Some (Compound (Arithmetic Add))
  | Punctuation Minus_equal -> Some (Compound (Arithmetic Subtract))
  | Punctuation Star_equal -> Some (Compound (Arithmetic Multiply))
  | Punctuation Slash_equal -> Some (Compound (Arithmetic Divide))
  | Punctuation Percent_equal -> Some (Compound (Arithmetic Remainder))
  | Punctuation Ampersand_equal -> Some (Compound (Bitwise Bit_and))
  | Punctuation Bar_equal -> Some (Compound (Bitwise Bit_or))
  | Punctuation Caret_equal -> Some (Compound (Bitwise Bit_xor))
  | Punctuation Shift_left_equal -> Some (Compound (Shift Shift_left))
  | Punctuation Shift_right_equal -> Some (Compound (Shift Shift_right))
  | _ -> None

let find_angle_closer cursor =
  let rec scan index depth =
    match (Cursor.lookup_token cursor index).kind with
    | Punctuation Less -> scan (index + 1) (depth + 1)
    | Punctuation Greater -> if depth = 1 then Some index else scan (index + 1) (depth - 1)
    | Punctuation Shift_right ->
        if depth = 2 then Some index else if depth > 2 then scan (index + 1) (depth - 2) else None
    | Punctuation (Open _) -> scan (Cursor.lookup_closer cursor index + 1) depth
    | Upper _ | Lower _ | Integer _
    | Punctuation (Comma | Colon | Colon_colon | Dot | Equal | Plus | Arrow)
    | Keyword (Self_type | Any | Fn | Mut | Own | Capability) ->
        scan (index + 1) depth
    | _ -> None
  in
  scan (Cursor.index cursor) 0

let skip_angle_brackets cursor =
  match find_angle_closer cursor with
  | None -> ()
  | Some closer ->
      let rec collect_angles index =
        if index > closer then []
        else
          let token = Cursor.lookup_token cursor index in
          match token.kind with
          | Punctuation (Less | Greater | Shift_right) -> token :: collect_angles (index + 1)
          | Punctuation (Open _) -> collect_angles (Cursor.lookup_closer cursor index + 1)
          | _ -> collect_angles (index + 1)
      in
      Habits.report_angle_brackets cursor ~angles:(collect_angles (Cursor.index cursor));
      Cursor.skip_to cursor (closer + 1)

let macro_follows cursor ~name_stop =
  let bang = Cursor.peek cursor and opener = Cursor.lookup_token cursor (Cursor.index cursor + 1) in
  bang.kind = Punctuation Bang && bang.span.start = name_stop
  && opener.span.start = bang.span.stop
  && match opener.kind with Punctuation (Open (Paren | Square)) -> true | _ -> false

let coalescing_follows cursor =
  let question = Cursor.peek cursor
  and second = Cursor.lookup_token cursor (Cursor.index cursor + 1) in
  let third = Cursor.peek_ahead cursor 2 in
  question.kind = Punctuation Question
  && second.span.start = question.span.stop
  && Atoms.begins_expression third
  &&
  match second.kind with
  | Punctuation Question -> (
      match third with Punctuation (Open _ | Minus | Dot_dot | Dot_dot_equal) -> false | _ -> true)
  | Punctuation Colon -> question.span.start > Cursor.compute_previous_stop cursor
  | _ -> false

let has_comma cursor ~opener =
  let closer = Cursor.lookup_closer cursor opener in
  let rec scan index =
    index < closer
    &&
    match (Cursor.lookup_token cursor index).kind with
    | Punctuation Comma -> true
    | Punctuation (Open _) -> scan (Cursor.lookup_closer cursor index + 1)
    | _ -> scan (index + 1)
  in
  scan (opener + 1)

let rec parse_type_expression cursor : Syntax.type_expression =
  Cursor.run_nested cursor @@ fun cursor ->
  let start = Cursor.index cursor in
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Keyword Self_type, _, _ ->
      Cursor.advance cursor;
      let associated =
        if Cursor.accept_punctuation cursor Dot then
          Some (Atoms.parse_upper_name cursor "an associated type after `Self.`")
        else None
      in
      Atoms.make_type_node cursor start (Self_type associated)
  | Keyword Any, _, _ ->
      Cursor.advance cursor;
      Atoms.make_type_node cursor start (Any_type (parse_path_type cursor))
  | Keyword Fn, _, _ ->
      Atoms.make_type_node cursor start (Function_type (parse_function_type cursor ~clauses:false))
  | Punctuation (Open Paren), _, _ -> parse_parenthesized_function_type cursor
  | Upper _, Punctuation Dot, Upper _ ->
      let parameter = Atoms.make_name cursor (Cursor.take cursor) in
      Cursor.advance cursor;
      Atoms.make_type_node cursor start
        (Associated (parameter, Atoms.parse_upper_name cursor "an associated type"))
  | (Upper _ | Lower _), _, _ ->
      Atoms.make_type_node cursor start (Path_type (parse_path_type cursor))
  | _ -> Cursor.fail cursor "a type"

and parse_path_type cursor : Syntax.path_type =
  let start = Cursor.index cursor in
  let path = Atoms.parse_upper_path cursor "a type name" in
  let arguments =
    if Cursor.is_punctuation cursor (Open Square) then parse_type_arguments cursor
    else begin
      if Cursor.is_punctuation cursor Less then skip_angle_brackets cursor;
      []
    end
  in
  { path; arguments; id = Cursor.allocate_id_from cursor start }

and parse_type_arguments cursor =
  let start = Cursor.index cursor in
  let arguments =
    Cursor.parse_bracketed cursor ~parse_item:parse_type_argument ~recover:(fun span ->
        Syntax.Type_argument { kind = Type_error; id = Cursor.allocate_id cursor span })
  in
  if arguments = [] then begin
    Cursor.report cursor Unexpected_token (Cursor.lookup_token cursor start).span
      "Type arguments cannot be empty.";
    raise Cursor.Failed
  end;
  arguments

and parse_type_argument cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Integer value, _ ->
      let token = Cursor.take cursor in
      Count (value, Cursor.allocate_id cursor (Cursor.make_definition_span cursor token.span))
  | Lower _, next when next <> Punctuation Colon_colon ->
      Count_name (Atoms.make_name cursor (Cursor.take cursor))
  | Upper _, Punctuation Equal ->
      let name = Atoms.make_name cursor (Cursor.take cursor) in
      Cursor.advance cursor;
      Constraint (name, parse_type_expression cursor)
  | _ -> Type_argument (parse_type_expression cursor)

and parse_function_type cursor ~clauses:with_clauses =
  let start = Cursor.index cursor in
  Cursor.expect_keyword cursor Fn;
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` after `fn` in a function type";
  let inputs =
    Cursor.parse_bracketed cursor
      ~parse_item:(fun cursor ->
        let name =
          match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
          | Lower _, Punctuation Colon ->
              let name = Atoms.make_name cursor (Cursor.take cursor) in
              Cursor.advance cursor;
              Some name
          | _ -> None
        in
        let mode = Atoms.parse_mode cursor in
        ({ name; mode; type_ = parse_type_expression cursor } : Syntax.function_input))
      ~recover:(fun span ->
        {
          name = None;
          mode = None;
          type_ = { kind = Type_error; id = Cursor.allocate_id cursor span };
        })
  in
  let output =
    if Cursor.accept_punctuation cursor Arrow then Some (parse_type_expression cursor) else None
  in
  let clauses =
    if with_clauses then
      let rec gather clauses =
        match Cursor.peek_kind cursor with
        | Keyword (Uses | Cost | Requires) -> gather (parse_clause cursor :: clauses)
        | Keyword (Ensures | Decreases) ->
            Cursor.fail cursor
              "`uses`, `cost`, or `requires`; a function type has no `ensures` or `decreases`"
        | _ -> List.rev clauses
      in
      gather []
    else []
  in
  let is_named (input : Syntax.function_input) = Option.is_some input.name in
  let has_requires =
    List.exists (fun (clause : Syntax.clause) ->
        match clause.kind with Requires _ -> true | _ -> false)
  in
  let span = (Cursor.lookup_token cursor start).span in
  if has_requires clauses then
    begin if not (List.for_all is_named inputs) then
      Cursor.report cursor Function_type_names span
        "A function type with `requires` names every input, as in `fn(index: UInt64)`, so that the \
         `requires` can mention them."
    end
  else if List.exists is_named inputs then
    Cursor.report cursor Function_type_names span
      "A function type names its inputs only when a `requires` mentions them; remove the names, \
       since calls through a function value pass arguments by position.";
  { inputs; output; clauses }

and parse_parenthesized_function_type cursor =
  let start = Cursor.index cursor in
  let closer = Cursor.lookup_closer cursor start in
  Cursor.advance cursor;
  match
    if (not (Cursor.is_keyword cursor Fn)) && has_comma cursor ~opener:start then
      Habits.report_tuple cursor ~opening:(Cursor.lookup_token cursor start);
    if not (Cursor.is_keyword cursor Fn) then
      Cursor.fail cursor
        "a function type; parentheses in a type only hold a function type with clauses";
    let function_type = parse_function_type cursor ~clauses:true in
    if function_type.clauses = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.lookup_token cursor start).span
        "Parentheses around a function type are only for its clauses; remove them.";
      raise Cursor.Failed
    end;
    if Cursor.index cursor < closer then
      Cursor.fail cursor "`)` after the clauses of the function type";
    function_type
  with
  | function_type ->
      Cursor.skip_to cursor (closer + 1);
      Atoms.make_type_node cursor start (Function_type function_type)
  | exception Cursor.Failed ->
      Cursor.skip_to cursor (closer + 1);
      Atoms.make_type_node cursor start Type_error

and parse_bounds cursor = Cursor.parse_separated cursor ~separator:Plus parse_path_type

and parse_generics cursor : Syntax.generic_parameter list =
  if Cursor.is_punctuation cursor Less then begin
    skip_angle_brackets cursor;
    []
  end
  else if not (Cursor.is_punctuation cursor (Open Square)) then []
  else
    let start = Cursor.index cursor in
    let parameters =
      Cursor.parse_bracketed cursor ~parse_item:parse_generic_parameter ~recover:(fun span ->
          { kind = Generic_error; id = Cursor.allocate_id cursor span })
    in
    if parameters = [] then begin
      Cursor.report cursor Unexpected_token (Cursor.lookup_token cursor start).span
        "Generic parameters cannot be empty.";
      raise Cursor.Failed
    end;
    parameters

and parse_generic_parameter cursor : Syntax.generic_parameter =
  let start = Cursor.index cursor in
  let kind =
    match Cursor.peek_kind cursor with
    | Upper _ ->
        let name = Atoms.make_name cursor (Cursor.take cursor) in
        Syntax.Type_parameter
          (name, if Cursor.accept_punctuation cursor Colon then parse_bounds cursor else [])
    | Lower _ ->
        let name = Atoms.make_name cursor (Cursor.take cursor) in
        Cursor.expect_punctuation cursor Colon;
        Value_parameter (name, parse_type_expression cursor)
    | _ -> Cursor.fail cursor "a generic parameter"
  in
  { kind; id = Cursor.allocate_id_from cursor start }

and parse_path_type_list cursor = Cursor.parse_separated cursor ~separator:Comma parse_path_type

and parse_capability_reference cursor : Syntax.capability_reference =
  let start = Cursor.index cursor in
  let kind =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
    | Keyword Self_type, _, _ ->
        Cursor.advance cursor;
        if not (Cursor.accept_punctuation cursor Dot) then
          Cursor.fail cursor
            "`.` and an associated capability set, as in `Self.Uses`; `Self` is a type, not a \
             capability";
        Syntax.Self_capabilities
          (Atoms.parse_upper_name cursor "an associated capability set after `Self.`")
    | Upper _, Punctuation Dot, Upper _ ->
        let parameter = Atoms.make_name cursor (Cursor.take cursor) in
        Cursor.advance cursor;
        Associated_capabilities
          (parameter, Atoms.parse_upper_name cursor "an associated capability set")
    | Lower "generic", Upper _, _ ->
        Cursor.advance cursor;
        Generic_capability (Atoms.parse_upper_name cursor "the name of a capability parameter")
    | _ -> Capability_path (parse_path_type cursor)
  in
  { kind; id = Cursor.allocate_id_from cursor start }

and parse_capability_list cursor =
  Cursor.parse_separated cursor ~separator:Comma parse_capability_reference

and parse_expression_list cursor =
  Cursor.parse_separated cursor ~separator:Comma (fun cursor -> parse_expression cursor)

and parse_clause cursor : Syntax.clause =
  let start = Cursor.index cursor in
  let keyword = Cursor.take cursor in
  let kind =
    match keyword.kind with
    | Keyword Uses -> Syntax.Uses (parse_capability_list cursor)
    | Keyword Requires -> Requires (parse_expression cursor)
    | Keyword Ensures -> Ensures (parse_expression cursor)
    | Keyword Decreases -> Decreases (parse_expression_list cursor)
    | Keyword Cost -> Cost (parse_cost cursor)
    | _ -> Cursor.fail cursor "a clause"
  in
  { kind; id = Cursor.allocate_id_from cursor start }

and parse_cost cursor =
  let amortized =
    match (Contextual_keyword.of_token (Cursor.peek_kind cursor), Cursor.peek_ahead cursor 1) with
    | Some Amortized, Lower _ ->
        Cursor.advance cursor;
        true
    | _ -> false
  in
  if Contextual_keyword.of_token (Cursor.peek_kind cursor) = Some Potential then begin
    Cursor.report cursor Misplaced_potential (Cursor.peek cursor).span
      "`cost potential` belongs to a type, and states the potential its values hold.";
    raise Cursor.Failed
  end;
  let resource =
    match
      Contextual_keyword.expect cursor ~accepted:Contextual_keyword.resources ~category:"a resource"
        ~expected:
          (Printf.sprintf "a resource: %s, or `calls(...)`"
             (String.concat ", "
                (List.map (fun metric -> "`" ^ Metric.show metric ^ "`") Metric.all)))
    with
    | Metric metric -> Syntax.Metric metric
    | _ -> Calls (parse_call_target cursor)
  in
  let bound =
    match Cursor.peek_kind cursor with
    | Punctuation Less_equal ->
        Cursor.advance cursor;
        Syntax.At_most (parse_expression cursor)
    | Punctuation Equal_equal ->
        Cursor.advance cursor;
        Exactly (parse_expression cursor)
    | _ ->
        ignore
          (Contextual_keyword.expect cursor ~accepted:[ O ] ~suggested:[ O ] ~category:"a bound"
             ~expected:"a bound: `O(...)`, `<=`, or `==`");
        Big_o (parse_parenthesized_expression cursor)
  in
  { amortized; resource; bound }

and parse_call_target cursor =
  let opener = Cursor.index cursor in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(` after `calls`";
  let closer = Cursor.lookup_closer cursor opener in
  Cursor.advance cursor;
  let target =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower _, next when next <> Punctuation Colon_colon ->
        Syntax.Call_parameter (Atoms.make_name cursor (Cursor.take cursor))
    | _ ->
        let capability = parse_path_type cursor in
        if Cursor.accept_punctuation cursor Dot then
          Call_method (capability, Atoms.lower_name cursor "a method name")
        else Call_capability capability
  in
  if Cursor.index cursor < closer then Cursor.fail cursor "`)` after the target of `calls`";
  Cursor.skip_to cursor (closer + 1);
  target

and parse_parenthesized_expression cursor =
  let opener = Cursor.index cursor in
  if not (Cursor.is_punctuation cursor (Open Paren)) then Cursor.fail cursor "`(`";
  let closer = Cursor.lookup_closer cursor opener in
  Cursor.advance cursor;
  let value = parse_expression cursor in
  if Cursor.index cursor < closer then Cursor.fail cursor "`)`";
  Cursor.skip_to cursor (closer + 1);
  value

and parse_expression ?(open_range = false) cursor =
  Cursor.run_nested cursor (fun cursor ->
      let start = Cursor.index cursor in
      let value = parse_pipes cursor start (parse_binary cursor ~level:0 ~open_range) in
      match Cursor.peek cursor with
      | { kind = Punctuation Question; _ } when coalescing_follows cursor ->
          parse_coalescing cursor start value
      | { kind = Punctuation Question; _ } as question -> (
          match conditional_follows (Cursor.peek_ahead cursor 1) with
          | true ->
              Cursor.advance cursor;
              parse_conditional cursor start value question
          | false -> value)
      | _ -> value)

and parse_pipes cursor start (value : Syntax.expression) =
  match Cursor.peek cursor with
  | { kind = Foreign Pipe_greater; _ } as operator ->
      Cursor.advance cursor;
      let callee = parse_binary cursor ~level:0 ~open_range:false in
      Habits.pipe_operator cursor ~value ~operator ~callee;
      parse_pipes cursor start (Atoms.make_error_expression cursor start)
  | _ -> value

and parse_coalescing cursor start (value : Syntax.expression) =
  let first = Cursor.take cursor in
  let second = Cursor.take cursor in
  let default = parse_binary cursor ~level:0 ~open_range:false in
  Habits.report_null_coalescing cursor ~value ~first ~second ~default;
  Atoms.make_error_expression cursor start

and parse_binary cursor ~level ~open_range =
  let start = Cursor.index cursor in
  let left =
    match Cursor.peek_kind cursor with
    | Punctuation ((Dot_dot | Dot_dot_equal) as range) when level <= range_level ->
        let token = Cursor.take cursor in
        if not open_range then open_range_error cursor token "start";
        let stop =
          parse_range_stop cursor ~open_range ~inclusive:(range = Dot_dot_equal) ~operator:token
        in
        Atoms.make_expression_node cursor start
          (Range
             {
               start = None;
               operator_id =
                 Cursor.allocate_id cursor (Cursor.make_definition_span cursor token.span);
               stop;
               inclusive = range = Dot_dot_equal;
             })
    | _ -> parse_prefix cursor
  in
  let rec climb ~chain_length (left : Syntax.expression) =
    match find_operator (Cursor.peek_kind cursor) with
    | Some operator when rank_operator operator >= level -> (
        Cursor.check_chain_length cursor ~chain_length;
        let climb = climb ~chain_length:(chain_length + 1) in
        let operator_token = Cursor.take cursor in
        let operator_id =
          Cursor.allocate_id cursor (Cursor.make_definition_span cursor operator_token.span)
        in
        match operator with
        | Binary_operator operator ->
            let right = parse_binary cursor ~level:(rank_binary operator + 1) ~open_range:false in
            climb
              (Atoms.make_expression_node cursor start
                 (Binary { operator; operator_id; left; right }))
        | Is_operator ->
            let pattern = Parse_pattern.parse_pattern cursor in
            climb
              (Atoms.make_expression_node cursor start (Is { value = left; operator_id; pattern }))
        | Range_operator inclusive ->
            let stop = parse_range_stop cursor ~open_range ~inclusive ~operator:operator_token in
            climb
              (Atoms.make_expression_node cursor start
                 (Range { start = Some left; operator_id; stop; inclusive })))
    | _ -> (
        match Cursor.peek cursor with
        | { kind = Foreign Star_star; _ } as power ->
            Cursor.check_chain_length cursor ~chain_length;
            Habits.report_power_operator cursor ~operator:power;
            Cursor.advance cursor;
            ignore (parse_prefix cursor);
            climb ~chain_length:(chain_length + 1) (Atoms.make_error_expression cursor start)
        | _ -> left)
  in
  climb ~chain_length:0 left

and parse_range_stop cursor ~open_range ~inclusive ~(operator : Token.t) =
  match Cursor.peek_kind cursor with
  | Punctuation (Close Square | Comma) when open_range ->
      if inclusive then
        Cursor.report cursor Open_range operator.span
          "A range that includes its end needs the end, as in `items[2..=4]`.";
      None
  | kind when Atoms.begins_expression kind ->
      Some (parse_binary cursor ~level:(range_level + 1) ~open_range:false)
  | _ ->
      open_range_error cursor operator "end";
      None

and open_range_message part =
  Printf.sprintf "A range without a%s %s is only allowed directly in brackets, as in `items[2..]`."
    (if part = "end" then "n" else "")
    part

and open_range_error cursor (token : Token.t) part =
  Cursor.report cursor Open_range token.span (open_range_message part);
  raise Cursor.Failed

and parse_prefix cursor : Syntax.expression =
  let start = Cursor.index cursor in
  let value =
    match Cursor.peek_kind cursor with
    | Punctuation Minus -> parse_prefix_operator cursor start Syntax.Negate
    | Punctuation Bang -> parse_prefix_operator cursor start Not
    | Punctuation Tilde -> parse_prefix_operator cursor start Complement
    | Keyword Mut ->
        Cursor.advance cursor;
        Atoms.make_expression_node cursor start (Mode (Mut, parse_postfix cursor))
    | Keyword Own ->
        Cursor.advance cursor;
        Atoms.make_expression_node cursor start (Mode (Own, parse_postfix cursor))
    | Keyword Any ->
        Cursor.advance cursor;
        Atoms.make_expression_node cursor start (Any (parse_postfix cursor))
    | Keyword (Forall | Exists) -> parse_quantified cursor
    | Keyword Echo ->
        Cursor.advance cursor;
        Atoms.make_expression_node cursor start (Echo (parse_expression cursor))
    | Keyword Return ->
        Cursor.advance cursor;
        let value =
          if Atoms.begins_expression (Cursor.peek_kind cursor) then Some (parse_expression cursor)
          else None
        in
        Atoms.make_expression_node cursor start (Return value)
    | Foreign Minus_minus ->
        let operator = Cursor.take cursor in
        let operand = Cursor.run_nested cursor parse_prefix in
        Habits.report_double_negation cursor ~operator ~operand;
        Atoms.make_error_expression cursor start
    | Punctuation Ampersand ->
        let before = Cursor.find_previous_token cursor in
        let ampersand = Cursor.take cursor in
        Habits.report_address_of cursor ~before ~ampersand ~next:(Cursor.peek cursor);
        Cursor.run_nested cursor parse_prefix
    | Punctuation (Bar | Or_or) -> parse_closure_bars cursor
    | _ -> parse_postfix cursor
  in
  match Cursor.peek_kind cursor with
  | Reserved As when not (Cursor.lookup_token cursor (Cursor.index cursor + 1)).line_break_before ->
      let as_token = Cursor.take cursor in
      let target = parse_type_expression cursor in
      Habits.report_as_conversion cursor ~value ~as_token ~target;
      Atoms.make_error_expression cursor start
  | _ -> value

and parse_prefix_operator cursor start operator =
  Cursor.advance cursor;
  let operand = Cursor.run_nested cursor parse_prefix in
  Atoms.make_expression_node cursor start (Prefix (operator, operand))

and parse_quantified cursor =
  let start = Cursor.index cursor in
  let quantifier = if (Cursor.take cursor).kind = Keyword Forall then Syntax.Forall else Exists in
  let binder =
    match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
    | Lower _, Punctuation Colon ->
        let name = Atoms.make_name cursor (Cursor.take cursor) in
        Cursor.advance cursor;
        Syntax.Binder_type (name, parse_type_expression cursor)
    | _ ->
        let pattern = Parse_pattern.parse_pattern cursor in
        Cursor.expect_keyword cursor In;
        Binder_in (pattern, parse_expression cursor)
  in
  Cursor.expect_punctuation cursor Fat_arrow;
  Atoms.make_expression_node cursor start
    (Quantified { quantifier; binder; body = parse_expression cursor })

and parse_closure_bars cursor =
  let start = Cursor.index cursor in
  let opening = Cursor.take cursor in
  let closing =
    if opening.kind = Punctuation Or_or then opening
    else
      let rec skip_parameters () =
        if Cursor.is_punctuation cursor Bar then Cursor.take cursor
        else begin
          ignore (Parse_pattern.parse_primary cursor);
          if not (Cursor.is_punctuation cursor Bar) then Cursor.expect_punctuation cursor Comma;
          skip_parameters ()
        end
      in
      skip_parameters ()
  in
  let body = parse_expression cursor in
  Habits.report_closure_bars cursor ~opening ~closing ~body
    ~is_before_else:(Cursor.is_keyword cursor Else);
  Atoms.make_error_expression cursor start

and parse_postfix cursor : Syntax.expression =
  let start = Cursor.index cursor in
  let rec with_postfixes ~chain_length (value : Syntax.expression) =
    let with_postfixes value =
      Cursor.check_chain_length cursor ~chain_length;
      with_postfixes ~chain_length:(chain_length + 1) value
    in
    match Cursor.peek_kind cursor with
    | Punctuation Dot -> (
        Cursor.advance cursor;
        match Cursor.peek_kind cursor with
        | Lower _ | Upper _ ->
            let name = Atoms.make_name cursor (Cursor.take cursor) in
            with_postfixes (Atoms.make_expression_node cursor start (Member (value, name)))
        | Integer _ | Float _ -> Habits.report_tuple_field cursor ~field:(Cursor.peek cursor)
        | _ -> Cursor.fail cursor "a name after `.`")
    | Punctuation (Open Square) ->
        if Cursor.peek_ahead cursor 1 = Punctuation (Close Square) then begin
          Cursor.advance cursor;
          Cursor.fail cursor "an index or type arguments"
        end;
        let opener = Cursor.index cursor in
        let items =
          Cursor.parse_bracketed cursor ~parse_item:parse_bracket_item ~recover:(fun span ->
              Syntax.Item { kind = Expression_error; id = Cursor.allocate_id cursor span })
        in
        let is_open_range = function
          | Syntax.Item { kind = Range { start = None; _ } | Range { stop = None; _ }; _ } -> true
          | _ -> false
        in
        (match items with
        | [ item ] when is_open_range item -> (
            match Cursor.lookup_token cursor (Cursor.lookup_closer cursor opener - 1) with
            | { kind = Punctuation Comma; span; _ } ->
                Cursor.report cursor Open_range span
                  "A range without a start or an end has no comma after it, as in `items[2..]`."
                  ~fixes:[ Diagnostic.fix "Remove the comma" [ Diagnostic.delete span ] ]
            | _ -> ())
        | _ -> ());
        if List.compare_length_with items 1 > 0 then
          List.iter
            (function
              | Syntax.Item
                  {
                    kind =
                      Range { start = None; operator_id; _ } | Range { stop = None; operator_id; _ };
                    _;
                  } ->
                  Cursor.report cursor Open_range
                    (Cursor.read_file_span cursor operator_id)
                    "A range without a start or an end must be the only item in its brackets, as \
                     in `items[2..]`."
              | _ -> ())
            items;
        with_postfixes (Atoms.make_expression_node cursor start (Bracket (value, items)))
    | Punctuation (Open Paren) ->
        let arguments = parse_arguments cursor in
        with_postfixes (Atoms.make_expression_node cursor start (Call (value, arguments)))
    | Punctuation Question when coalescing_follows cursor -> value
    | Punctuation Question when not (conditional_follows (Cursor.peek_ahead cursor 1)) ->
        Cursor.advance cursor;
        with_postfixes (Atoms.make_expression_node cursor start (Try value))
    | Keyword With ->
        Cursor.advance cursor;
        if not (Cursor.is_punctuation cursor (Open Paren)) then
          Cursor.fail cursor "`(` after `with`";
        let updates =
          Cursor.parse_bracketed cursor ~parse_item:update ~recover:(fun span ->
              { kind = Update_error; id = Cursor.allocate_id cursor span })
        in
        with_postfixes (Atoms.make_expression_node cursor start (With (value, updates)))
    | _ -> value
  in
  with_postfixes ~chain_length:0 (parse_primary cursor)

and conditional_follows = function
  | Punctuation (Open _ | Minus | Dot_dot | Dot_dot_equal) -> false
  | kind -> Atoms.begins_expression kind

and parse_conditional cursor start condition question =
  let then_ = parse_expression cursor in
  Cursor.expect_punctuation cursor Colon;
  let else_ = parse_expression cursor in
  Habits.report_conditional cursor ~condition ~then_ ~else_ ~question;
  Atoms.make_error_expression cursor start

and parse_bracket_item cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Upper _, Punctuation Equal ->
      let name = Atoms.make_name cursor (Cursor.take cursor) in
      Cursor.advance cursor;
      Item_constraint (name, parse_type_expression cursor)
  | _ -> Item (parse_expression cursor ~open_range:true)

and parse_arguments cursor =
  Cursor.parse_bracketed cursor ~parse_item:parse_argument ~recover:(fun span ->
      {
        Syntax.label = None;
        value = { kind = Expression_error; id = Cursor.allocate_id cursor span };
      })

and parse_argument cursor =
  match (Cursor.peek_kind cursor, Cursor.peek_ahead cursor 1) with
  | Lower _, Punctuation Colon ->
      let label = Atoms.make_name cursor (Cursor.take cursor) in
      Cursor.advance cursor;
      { label = Some label; value = parse_expression cursor }
  | _ -> { label = None; value = parse_expression cursor }

and update cursor : Syntax.update =
  let start = Cursor.index cursor in
  let field = Atoms.lower_name cursor "a field name" in
  let rec parse_field_path fields =
    if Cursor.accept_punctuation cursor Dot then
      parse_field_path (Atoms.lower_name cursor "a field name" :: fields)
    else List.rev fields
  in
  let path = parse_field_path [] in
  let value =
    if Cursor.accept_punctuation cursor Colon then Some (parse_expression cursor) else None
  in
  { kind = Update { field; path; value }; id = Cursor.allocate_id_from cursor start }

and parse_primary cursor : Syntax.expression =
  let start = Cursor.index cursor in
  let parse_simple kind =
    Cursor.advance cursor;
    Atoms.make_expression_node cursor start kind
  in
  match Cursor.peek_kind cursor with
  | Integer value -> parse_simple (Integer value)
  | Float value -> parse_simple (Float value)
  | String literal ->
      Atoms.make_expression_node cursor start
        (String (parse_string_literal cursor ~start ~modules:[] literal))
  | Keyword True -> parse_simple True
  | Keyword False -> parse_simple False
  | Keyword Todo -> parse_keyword_macro cursor (parse_simple Todo)
  | Keyword Unreachable -> parse_keyword_macro cursor (parse_simple Unreachable)
  | Keyword Break -> parse_simple Break
  | Keyword Continue -> parse_simple Continue
  | Keyword Self_value -> parse_simple Self_value
  | Keyword Self_type -> parse_simple Self_type_value
  | Lower _ | Upper _ -> parse_name_expression cursor start
  | Punctuation (Open Paren) -> (
      let closer = Cursor.lookup_closer cursor start in
      Cursor.advance cursor;
      match
        let inner = parse_expression cursor in
        if Cursor.is_punctuation cursor Comma then
          Habits.report_tuple cursor ~opening:(Cursor.lookup_token cursor start);
        if Cursor.index cursor < closer then Cursor.fail cursor "`)`";
        inner
      with
      | inner ->
          Cursor.skip_to cursor (closer + 1);
          Atoms.make_expression_node cursor start (Parenthesized inner)
      | exception Cursor.Failed ->
          Cursor.skip_to cursor (closer + 1);
          Atoms.make_error_expression cursor start)
  | Punctuation (Open Square) -> parse_collection cursor
  | Punctuation (Open Curly) -> Atoms.make_expression_node cursor start (Block (parse_block cursor))
  | Keyword Fn -> parse_lambda cursor
  | Keyword If -> parse_if_expression cursor
  | Keyword Match -> match_expression cursor
  | Keyword Provide ->
      Cursor.advance cursor;
      let implementations = parse_expression_list cursor in
      Atoms.make_expression_node cursor start
        (Provide { implementations; body = parse_body cursor })
  | _ -> Cursor.fail cursor "an expression"

and parse_name_expression cursor start =
  let modules = Atoms.parse_module_prefix cursor in
  match Cursor.peek_kind cursor with
  | Lower _ ->
      let token = Cursor.take cursor in
      let name = Atoms.make_name cursor token in
      if modules = [] && macro_follows cursor ~name_stop:token.span.stop then
        parse_macro cursor start name
      else Atoms.make_expression_node cursor start (Name { modules; last = name })
  | Upper _ ->
      let name = Atoms.make_name cursor (Cursor.take cursor) in
      let value =
        parse_path_separators cursor start
          (Atoms.make_expression_node cursor start (Name { modules; last = name }))
      in
      let value = parse_path_separators cursor start (parse_angle_arguments cursor start value) in
      if brace_record_follows cursor then parse_brace_record cursor start value else value
  | String ({ tag = Some _; _ } as literal) ->
      Atoms.make_expression_node cursor start
        (String (parse_string_literal cursor ~start ~modules literal))
  | Punctuation Less -> parse_turbofish cursor start
  | _ -> Cursor.fail cursor "a name after `::`"

and parse_path_separators cursor start (value : Syntax.expression) =
  match (Cursor.peek cursor, Cursor.peek_ahead cursor 1) with
  | ({ kind = Punctuation Colon_colon; _ } as separator), (Upper _ | Lower _) ->
      Habits.report_path_separator cursor ~separator;
      Cursor.advance cursor;
      let name = Atoms.make_name cursor (Cursor.take cursor) in
      parse_path_separators cursor start
        (Atoms.make_expression_node cursor start (Member (value, name)))
  | _ -> value

and parse_angle_arguments cursor start (value : Syntax.expression) =
  let follows_closer closer =
    match (Cursor.lookup_token cursor (closer + 1)).kind with
    | Punctuation (Dot | Open Paren | Colon_colon) -> true
    | _ -> false
  in
  match if Cursor.is_punctuation cursor Less then find_angle_closer cursor else None with
  | Some closer when follows_closer closer ->
      skip_angle_brackets cursor;
      Atoms.make_error_expression cursor start
  | _ -> value

and parse_macro cursor start (name : Syntax.name) =
  let bang = Cursor.take cursor in
  let opening = Cursor.peek cursor in
  Habits.report_macro_call cursor ~name ~bang ~opening;
  (match opening.kind with
  | Punctuation (Open Square) -> ignore (parse_collection cursor)
  | _ -> ignore (parse_arguments cursor));
  Atoms.make_error_expression cursor start

and parse_keyword_macro cursor (value : Syntax.expression) =
  if macro_follows cursor ~name_stop:(Cursor.compute_previous_stop cursor) then begin
    let bang = Cursor.take cursor in
    let closer = Cursor.lookup_closer cursor (Cursor.index cursor) in
    Habits.report_keyword_macro cursor ~bang
      ~closing:(Cursor.lookup_token cursor closer)
      ~has_arguments:(closer > Cursor.index cursor + 1);
    Cursor.skip_to cursor (closer + 1)
  end;
  value

and brace_record_follows cursor =
  let opening = Cursor.peek cursor in
  opening.kind = Punctuation (Open Curly)
  && (not opening.line_break_before)
  &&
  match (Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Lower _, Punctuation Colon -> true
  | _ -> false

and parse_brace_record cursor start (record : Syntax.expression) =
  let opening = Cursor.peek cursor in
  let closer = Cursor.lookup_closer cursor (Cursor.index cursor) in
  Cursor.advance cursor;
  let first = Cursor.peek cursor in
  let rec skip_arguments () =
    if Cursor.index cursor < closer then begin
      ignore (parse_argument cursor);
      if Cursor.index cursor < closer then Cursor.expect_punctuation cursor Comma;
      skip_arguments ()
    end
  in
  skip_arguments ();
  let last_stop = Cursor.compute_previous_stop cursor in
  let closing = Cursor.lookup_token cursor closer in
  Cursor.skip_to cursor (closer + 1);
  Habits.report_brace_record cursor ~name_stop:(Cursor.read_file_span cursor record.id).stop
    ~opening ~first ~last_stop ~closing;
  Atoms.make_error_expression cursor start

and parse_turbofish cursor start =
  let colons = Cursor.lookup_token cursor (Cursor.index cursor - 1) in
  let less = Cursor.take cursor in
  ignore (Cursor.parse_separated cursor ~separator:Comma parse_type_expression);
  if not (Cursor.is_punctuation cursor Greater) then
    Cursor.fail cursor "`>` after the type arguments";
  let greater = Cursor.take cursor in
  Habits.report_turbofish cursor ~colons ~less ~greater;
  Atoms.make_error_expression cursor start

and parse_string_literal cursor ~start ~modules literal =
  Atoms.make_string_literal cursor ~start ~modules literal
    ~parse_interpolation:(parse_interpolation cursor)

and parse_interpolation cursor (inner : Token.interpolation) : Syntax.expression =
  let nested = Cursor.enter_interpolation cursor inner in
  if Cursor.is_at_end nested then
    {
      kind = Expression_error;
      id = Cursor.allocate_id cursor (Cursor.make_definition_span cursor inner.span);
    }
  else
    match
      let value = parse_expression nested in
      if not (Cursor.is_at_end nested) then Cursor.fail nested "the end of the interpolation";
      value
    with
    | value -> value
    | exception Cursor.Failed ->
        {
          kind = Expression_error;
          id = Cursor.allocate_id cursor (Cursor.make_definition_span cursor inner.span);
        }

and parse_collection cursor =
  let start = Cursor.index cursor in
  match (Cursor.peek_ahead cursor 1, Cursor.peek_ahead cursor 2) with
  | Punctuation Colon, Punctuation (Close Square) ->
      Cursor.advance cursor;
      Cursor.advance cursor;
      Cursor.advance cursor;
      Atoms.make_expression_node cursor start (Map [])
  | _ -> (
      let parse_element cursor =
        let key = parse_expression cursor in
        let value =
          if Cursor.accept_punctuation cursor Colon then Some (parse_expression cursor) else None
        in
        (key, value)
      in
      let elements =
        Cursor.parse_bracketed cursor ~parse_item:parse_element ~recover:(fun span ->
            ({ kind = Expression_error; id = Cursor.allocate_id cursor span }, None))
      in
      let is_error ((key : Syntax.expression), _) = key.kind = Expression_error in
      let entries =
        List.filter_map (fun (key, value) -> Option.map (fun value -> (key, value)) value) elements
      in
      match elements with
      | first :: _ when (not (is_error first)) && snd first <> None ->
          if List.length entries = List.length elements then
            Atoms.make_expression_node cursor start (Map entries)
          else
            parse_mixed_collection cursor start
              (List.find (fun (_, value) -> value = None) elements)
      | _ -> (
          match List.find_opt (fun (_, value) -> value <> None) elements with
          | None -> Atoms.make_expression_node cursor start (List (List.map fst elements))
          | Some entry -> parse_mixed_collection cursor start entry))

and parse_mixed_collection cursor start ((key : Syntax.expression), _) =
  Cursor.report cursor Unexpected_token
    (Cursor.read_file_span cursor key.id)
    "A collection holds either list elements or map entries, `key: value`, not both.";
  Atoms.make_error_expression cursor start

and parse_lambda cursor =
  let start = Cursor.index cursor in
  Cursor.advance cursor;
  if not (Cursor.is_punctuation cursor (Open Paren)) then
    Cursor.fail cursor "`(` after `fn` in a lambda";
  let parse_parameter cursor =
    let pattern = Parse_pattern.parse_pattern cursor in
    if Cursor.is_punctuation cursor Colon then begin
      let from = Cursor.compute_previous_stop cursor in
      Cursor.advance cursor;
      ignore (Atoms.parse_mode cursor);
      ignore (parse_type_expression cursor);
      Habits.report_lambda_annotation cursor ~from ~stop:(Cursor.compute_previous_stop cursor)
    end;
    pattern
  in
  let parameters =
    Cursor.parse_bracketed cursor ~parse_item:parse_parameter ~recover:(fun span ->
        { kind = Pattern_error; id = Cursor.allocate_id cursor span })
  in
  if Cursor.is_punctuation cursor Arrow then begin
    let from = Cursor.compute_previous_stop cursor in
    Cursor.advance cursor;
    ignore (parse_type_expression cursor);
    Habits.report_lambda_annotation cursor ~from ~stop:(Cursor.compute_previous_stop cursor)
  end;
  Atoms.make_expression_node cursor start (Lambda { parameters; body = parse_body cursor })

and parse_if_expression ?(chain_length = 0) cursor =
  let start = Cursor.index cursor in
  Cursor.expect_keyword cursor If;
  let condition = parse_expression cursor in
  let then_ = parse_body cursor in
  Atoms.make_expression_node cursor start
    (If { condition; then_; else_ = parse_else_branch cursor ~chain_length })

and parse_else_branch cursor ~chain_length =
  if Cursor.accept_keyword cursor Else then
    if Cursor.is_keyword cursor If then begin
      Cursor.check_chain_length cursor ~chain_length;
      Some (Else_if (parse_if_expression cursor ~chain_length:(chain_length + 1)))
    end
    else Some (Else (parse_body cursor))
  else None

and match_expression cursor =
  let start = Cursor.index cursor in
  Cursor.advance cursor;
  let scrutinees = parse_expression_list cursor in
  expect_body_opening cursor;
  let arms =
    Cursor.parse_lines cursor ~parse_item:parse_arm ~recover:(fun span ->
        {
          rows = [];
          guard = None;
          body = { kind = Statement_error; id = Cursor.allocate_id cursor span };
          id = Cursor.allocate_id cursor span;
        })
  in
  Atoms.make_expression_node cursor start (Match { scrutinees; arms })

and parse_arm cursor : Syntax.arm =
  let start = Cursor.index cursor in
  let rows = Cursor.parse_separated cursor ~separator:Bar parse_row in
  let guard = if Cursor.accept_keyword cursor If then Some (parse_expression cursor) else None in
  Cursor.expect_punctuation cursor Fat_arrow;
  let body = parse_statement cursor in
  (match Cursor.peek cursor with
  | { kind = Punctuation Comma; _ } as comma ->
      Habits.match_arm_comma cursor ~comma;
      Cursor.advance cursor
  | _ -> ());
  { rows; guard; body; id = Cursor.allocate_id_from cursor start }

and parse_row cursor : Syntax.row =
  let start = Cursor.index cursor in
  let patterns = Cursor.parse_separated cursor ~separator:Comma Parse_pattern.parse_primary in
  { patterns; id = Cursor.allocate_id_from cursor start }

and opens_body cursor =
  Cursor.is_punctuation cursor (Open Curly)
  || (Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly))

and expect_body_opening cursor =
  if Cursor.is cursor Newline && Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) then
    Cursor.advance cursor;
  if not (Cursor.is_punctuation cursor (Open Curly)) then Cursor.fail cursor "`{` to start the body"

and parse_body cursor =
  expect_body_opening cursor;
  parse_block cursor

and parse_block cursor : Syntax.block =
  Cursor.run_nested cursor @@ fun cursor ->
  let start = Cursor.index cursor in
  let previous = ref None in
  let parse_item cursor =
    let statement = parse_statement_line cursor ~previous:!previous in
    previous := Some statement;
    statement
  in
  let statements =
    Cursor.parse_lines cursor ~parse_item ~recover:(fun span ->
        previous := None;
        { kind = Statement_error; id = Cursor.allocate_id cursor span })
  in
  { Syntax.statements; id = Cursor.allocate_id_from cursor start }

and parse_statement_line cursor ~previous : Syntax.statement =
  match (Cursor.peek cursor, previous) with
  | ( ({ kind = Lower "elif"; _ } as elif_token),
      Some ({ kind = Expression { kind = If _; _ }; _ } as previous_if) )
    when Atoms.begins_expression (Cursor.peek_ahead cursor 1) ->
      let start = Cursor.index cursor in
      Habits.report_elif cursor ~previous_stop:(Cursor.read_file_span cursor previous_if.id).stop
        ~elif_token;
      Cursor.advance cursor;
      let condition = parse_expression cursor in
      let then_ = parse_body cursor in
      let else_ = parse_else_branch cursor ~chain_length:0 in
      let value = Atoms.make_expression_node cursor start (If { condition; then_; else_ }) in
      { kind = Expression value; id = Cursor.allocate_id cursor (Cursor.read_span cursor value.id) }
  | _ ->
      let statement = parse_statement cursor in
      parse_trailing_habits cursor statement

and parse_trailing_habits cursor (statement : Syntax.statement) =
  match (Cursor.peek_kind cursor, statement.kind) with
  | Foreign (Plus_plus | Minus_minus), Expression target
    when match Cursor.peek_ahead cursor 1 with
         | Newline | End_of_file | Punctuation (Close _) -> true
         | _ -> false ->
      let operator = Cursor.take cursor in
      Habits.increment cursor ~target ~operator;
      parse_statement_error_through cursor statement
        (Cursor.make_definition_span cursor operator.span)
  | Punctuation (Open Curly), _ when not (Cursor.peek cursor).line_break_before ->
      parse_trailing_lambda cursor statement
  | _ -> statement

and parse_statement_error_through cursor (statement : Syntax.statement)
    (last : Source.Definition_span.t) =
  Cursor.set_span cursor statement.id
    (Source.Definition_span.make (Cursor.read_span cursor statement.id).start last.stop);
  { statement with kind = Statement_error }

and find_trailing_callee (statement : Syntax.statement) =
  let rec find_rightmost (value : Syntax.expression) =
    match value.kind with
    | Name _ | Member _ -> Some value
    | Binary { right = inner; _ } | Return (Some inner) | Echo inner | Mode (_, inner) | Any inner
      ->
        find_rightmost inner
    | _ -> None
  in
  match statement.kind with
  | Expression value | Let { value; _ } | Assignment { value; _ } -> find_rightmost value
  | _ -> None

and list_uses_of_it (tokens : Token.t array) =
  List.concat_map
    (fun (token : Token.t) ->
      match token.kind with
      | Lower "it" -> [ token ]
      | String literal ->
          List.concat_map
            (fun (inner : Token.interpolation) -> list_uses_of_it inner.tokens)
            (Array.to_list (Token.list_interpolations literal))
      | _ -> [])
    (Array.to_list tokens)

and parse_trailing_lambda cursor (statement : Syntax.statement) =
  let opening = Cursor.peek cursor in
  let closing = Cursor.lookup_token cursor (Cursor.lookup_closer cursor (Cursor.index cursor)) in
  match (list_uses_of_it (Cursor.group cursor), find_trailing_callee statement) with
  | (_ :: _ as uses), Some callee ->
      Habits.report_trailing_lambda cursor ~callee
        ~parameter:(Habits.derive_parameter_name callee)
        ~opening ~closing ~uses;
      ignore (parse_block cursor);
      parse_statement_error_through cursor statement
        (Cursor.make_definition_span cursor closing.span)
  | _ -> statement

and parse_statement cursor : Syntax.statement =
  let start = Cursor.index cursor in
  let make_statement_node kind : Syntax.statement =
    { kind; id = Cursor.allocate_id_from cursor start }
  in
  match Cursor.peek_kind cursor with
  | Keyword Let ->
      let let_token = Cursor.take cursor in
      if Cursor.is_keyword cursor Mut then begin
        let mut_token = Cursor.take cursor in
        Habits.report_let_mut cursor ~let_token ~mut_token;
        make_statement_node (parse_binding cursor ~is_var:true)
      end
      else make_statement_node (parse_binding cursor ~is_var:false)
  | Keyword Var ->
      Cursor.advance cursor;
      make_statement_node (parse_binding cursor ~is_var:true)
  | Keyword For ->
      Cursor.advance cursor;
      make_statement_node (parse_for_loop cursor ~mode:Syntax.Sequential)
  | Keyword While ->
      Cursor.advance cursor;
      let condition = parse_expression cursor in
      let clauses = parse_loop_clauses cursor in
      make_statement_node (While { condition; clauses; body = parse_body cursor })
  | Keyword Parallel ->
      Cursor.advance cursor;
      if Cursor.accept_keyword cursor For then
        make_statement_node (parse_for_loop cursor ~mode:Parallel_loop)
      else make_statement_node (Parallel (parse_body cursor))
  | Keyword Concurrent ->
      Cursor.advance cursor;
      if Cursor.accept_keyword cursor For then
        make_statement_node (parse_for_loop cursor ~mode:Concurrent_loop)
      else make_statement_node (Concurrent (parse_body cursor))
  | Keyword Proof ->
      Cursor.advance cursor;
      make_statement_node (Proof (parse_body cursor))
  | Keyword Assert ->
      Cursor.advance cursor;
      let value = parse_expression cursor in
      let by_bit_vector =
        match
          ( Contextual_keyword.of_token (Cursor.peek_kind cursor),
            Contextual_keyword.of_token (Cursor.peek_ahead cursor 1) )
        with
        | Some By, Some Bit_vector ->
            Cursor.advance cursor;
            Cursor.advance cursor;
            true
        | _ -> false
      in
      make_statement_node (Assert { value; by_bit_vector })
  | Reserved Loop when Cursor.peek_ahead cursor 1 = Punctuation (Open Curly) ->
      let loop_token = Cursor.take cursor in
      Habits.report_loop cursor ~loop_token;
      ignore (parse_body cursor);
      make_statement_node Statement_error
  | _ -> (
      let target = parse_expression cursor in
      match (find_assignment_operator (Cursor.peek_kind cursor), Cursor.peek cursor) with
      | Some operator, _ ->
          Cursor.advance cursor;
          make_statement_node (Assignment { target; operator; value = parse_expression cursor })
      | None, ({ kind = Foreign Colon_equal; _ } as operator) ->
          Cursor.advance cursor;
          Habits.report_short_declaration cursor ~target ~operator;
          make_statement_node
            (Assignment { target; operator = Assign; value = parse_expression cursor })
      | None, _ -> make_statement_node (Expression target))

and parse_binding cursor ~is_var =
  let pattern = Parse_pattern.parse_pattern cursor in
  let annotation =
    if Cursor.accept_punctuation cursor Colon then Some (parse_type_expression cursor) else None
  in
  Cursor.expect_punctuation cursor Equal;
  let value = parse_expression cursor in
  let else_ =
    if Cursor.is_keyword cursor Else then begin
      (match Cursor.find_previous_token cursor with
      | Some { kind = Punctuation (Close Curly); _ } ->
          let span = Cursor.read_file_span cursor value.id in
          Cursor.report cursor Let_else_brace (Cursor.peek cursor).span
            "The expression before the `else` of a `let ... else` cannot end with `}`; put it in \
             parentheses."
            ~fixes:
              [
                Diagnostic.fix "Put the expression in parentheses"
                  [
                    Diagnostic.insert (Source.make_zero_width span.start) "(";
                    Diagnostic.insert (Source.make_zero_width span.stop) ")";
                  ];
              ]
      | _ -> ());
      Cursor.advance cursor;
      Some (parse_body cursor)
    end
    else None
  in
  Let { is_var; pattern; annotation; value; else_ }

and parse_for_loop cursor ~mode =
  let pattern = Parse_pattern.parse_pattern cursor in
  let annotation =
    if Cursor.accept_punctuation cursor Colon then Some (parse_type_expression cursor) else None
  in
  Cursor.expect_keyword cursor In;
  let iterable = parse_expression cursor in
  (match iterable.kind with
  | Range { stop = Some { kind = Block _; _ }; operator_id; _ } when not (opens_body cursor) ->
      Cursor.report cursor Open_range
        (Cursor.read_file_span cursor operator_id)
        (open_range_message "end");
      raise Cursor.Failed
  | _ -> ());
  let clauses = parse_loop_clauses cursor in
  For { mode; pattern; annotation; iterable; clauses; body = parse_body cursor }

and parse_loop_clauses cursor =
  let rec gather clauses =
    let start = Cursor.index cursor in
    match Cursor.peek_kind cursor with
    | Keyword Cost ->
        let keyword = Cursor.take cursor in
        let cost = parse_cost cursor in
        if cost.amortized then
          Cursor.report cursor Loop_cost_bound keyword.span
            "A loop's `cost` bounds the loop's cost so far, so it is never `amortized`. Potential \
             belongs to the values the loop mutates, which the function's own `cost` accounts for.";
        gather
          (({ kind = Loop_cost cost; id = Cursor.allocate_id_from cursor start }
             : Syntax.loop_clause)
          :: clauses)
    | Keyword Invariant ->
        Cursor.advance cursor;
        let value = parse_expression cursor in
        gather
          (({ kind = Invariant value; id = Cursor.allocate_id_from cursor start }
             : Syntax.loop_clause)
          :: clauses)
    | Keyword Decreases ->
        let keyword = Cursor.take cursor in
        if
          List.exists
            (fun (clause : Syntax.loop_clause) ->
              match clause.kind with Loop_decreases _ -> true | _ -> false)
            clauses
        then
          Cursor.report cursor Repeated_clause keyword.span
            "A loop has at most one `decreases` clause; list several measures in one, separated by \
             commas.";
        let measures = parse_expression_list cursor in
        gather
          (({ kind = Loop_decreases measures; id = Cursor.allocate_id_from cursor start }
             : Syntax.loop_clause)
          :: clauses)
    | _ -> List.rev clauses
  in
  gather []

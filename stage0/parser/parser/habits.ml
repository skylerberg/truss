let read_span cursor id = Cursor.read_file_span cursor id

let extend_with_trailing_space (token : Token.t) ~(next : Token.t) =
  Source.make_span token.span.start next.span.start

let increment cursor ~(target : Syntax.expression) ~(operator : Token.t) =
  Cursor.report cursor operator.span
    (Increment
       { is_increment = operator.kind = Foreign Plus_plus; target = read_span cursor target.id })

let report_double_negation cursor ~(operator : Token.t) ~(operand : Syntax.expression) =
  Cursor.report cursor operator.span (Double_negation { operand = read_span cursor operand.id })

let match_arm_comma cursor ~(comma : Token.t) ~(next : Token.t) =
  let is_arm_end =
    next.line_break_before
    || match next.kind with Newline | Punctuation (Close Curly) -> true | _ -> false
  in
  Cursor.report cursor comma.span
    (Match_arm_comma { next_arm = (if is_arm_end then None else Some next.span) })

let report_conditional cursor ~(condition : Syntax.expression) ~(then_ : Syntax.expression)
    ~(else_ : Syntax.expression) ~(question : Token.t) =
  Cursor.report cursor question.span
    (Conditional_operator
       {
         condition = read_span cursor condition.id;
         then_ = read_span cursor then_.id;
         else_ = read_span cursor else_.id;
       })

let report_let_mut cursor ~(let_token : Token.t) ~(mut_token : Token.t) =
  Cursor.report cursor mut_token.span
    (Let_mut { let_mut = Source.make_span let_token.span.start mut_token.span.stop })

let report_address_of cursor ~(before : Token.t option) ~(ampersand : Token.t) ~(next : Token.t) =
  let needs_space =
    match before with
    | Some { kind = Upper _ | Lower _ | Keyword _ | Reserved _ | Integer _ | Float _; span; _ } ->
        span.stop = ampersand.span.start
    | _ -> false
  in
  Cursor.report cursor ampersand.span
    (Address_of
       {
         is_mut = next.kind = Keyword Mut;
         removed = extend_with_trailing_space ampersand ~next;
         needs_space;
       })

let report_closure_bars cursor ~(opening : Token.t) ~(closing : Token.t) ~(body : Syntax.expression)
    ~is_before_else =
  Cursor.report cursor opening.span
    (Closure_bars
       {
         closing = closing.span;
         body = read_span cursor body.id;
         has_parameters = opening.kind <> Punctuation Or_or;
         is_block = (match body.kind with Block _ -> true | _ -> false);
         is_before_else;
       })

let report_brace_record cursor ~(name_stop : int) ~(opening : Token.t) ~(first : Token.t)
    ~(last_stop : int) ~(closing : Token.t) =
  Cursor.report cursor opening.span
    (Brace_record
       {
         opening = Source.make_span name_stop first.span.start;
         closing = Source.make_span last_stop closing.span.stop;
       })

let report_turbofish cursor ~(colons : Token.t) ~(less : Token.t) ~(greater : Token.t) =
  Cursor.report cursor less.span
    (Turbofish
       { opening = Source.make_span colons.span.start less.span.stop; closing = greater.span })

let report_angle_brackets cursor ~(angles : Token.t list) =
  Cursor.report cursor (List.hd angles).span
    (Angle_brackets
       (List.map
          (fun (token : Token.t) : (Source.span * Syntax_catalog.Parsing.angle_bracket) ->
            ( token.span,
              match token.kind with
              | Punctuation Less -> Opening_angle
              | Punctuation Shift_right -> Double_closing_angle
              | _ -> Closing_angle ))
          angles))

let report_qualified_variant cursor ~qualifier_start ~(variant : Syntax.name) =
  Cursor.report cursor
    (Source.make_span qualifier_start (read_span cursor variant.id).start)
    (Qualified_variant { variant = variant.text })

let classify_macro : string -> Syntax_catalog.Parsing.macro = function
  | "println" | "print" | "eprintln" | "eprint" -> Print_macro
  | "format" -> Format_macro
  | "vec" -> Vector_macro
  | "assert" | "assert_eq" | "assert_ne" | "debug_assert" -> Assertion_macro
  | "dbg" -> Debug_macro
  | "panic" -> Panic_macro
  | _ -> Other_macro

let report_macro_call cursor ~(name : Syntax.name) ~(bang : Token.t) ~(opening : Token.t) =
  Cursor.report cursor bang.span
    (Macro_call
       {
         name = name.text;
         macro = classify_macro name.text;
         list_call =
           (match (name.text, opening.kind) with
           | "vec", Punctuation (Open Square) ->
               Some (Source.make_span (read_span cursor name.id).start bang.span.stop)
           | _ -> None);
       })

let report_keyword_macro cursor ~(bang : Token.t) ~(closing : Token.t) ~has_arguments =
  Cursor.report cursor bang.span
    (Keyword_macro
       {
         call =
           (if has_arguments then None
            else Some (Source.make_span bang.span.start closing.span.stop));
       })

let report_tuple cursor ~(opening : Token.t) =
  Cursor.report cursor opening.span Tuple;
  raise Cursor.Failed

let report_tuple_field cursor ~(field : Token.t) =
  Cursor.report cursor field.span Tuple_field;
  raise Cursor.Failed

let report_power_operator cursor ~(operator : Token.t) =
  Cursor.report cursor operator.span Power_operator

let report_short_declaration cursor ~(target : Syntax.expression) ~(operator : Token.t) =
  Cursor.report cursor operator.span
    (Short_declaration
       { name = (match target.kind with Name _ -> Some (read_span cursor target.id) | _ -> None) })

let pipe_operator cursor ~(value : Syntax.expression) ~(operator : Token.t)
    ~(callee : Syntax.expression) =
  let rec is_path (candidate : Syntax.expression) =
    match candidate.kind with
    | Name _ -> true
    | Member (receiver, _) -> is_path receiver
    | _ -> false
  in
  Cursor.report cursor operator.span
    (Pipe_operator
       {
         call =
           (if is_path callee then
              Some { value = read_span cursor value.id; callee = read_span cursor callee.id }
            else None);
       })

let report_lambda_annotation cursor ~from ~stop =
  Cursor.report cursor (Source.make_span from stop) Lambda_annotation

let report_impl_parameters cursor ~(opening : Token.t) ~(closing : Token.t) ~has_bounds =
  Cursor.report cursor opening.span
    (Impl_parameters
       {
         parameters =
           (if has_bounds then None
            else Some (Source.make_span opening.span.start closing.span.stop));
       })

let report_null_coalescing cursor ~(value : Syntax.expression) ~(first : Token.t)
    ~(second : Token.t) ~(default : Syntax.expression) =
  Cursor.report cursor first.span
    (Null_coalescing
       {
         written = (match second.kind with Punctuation Colon -> "?:" | _ -> "??");
         value = read_span cursor value.id;
         default = read_span cursor default.id;
         needs_parentheses =
           (match value.kind with
           | Binary _ | Is _ | Range _ | Prefix _ | Mode _ | Quantified _ | Echo _ | Return _ ->
               true
           | _ -> false);
       })

let report_trailing_lambda cursor ~(callee : Syntax.expression) ~(opening : Token.t)
    ~(closing : Token.t) ~(next : Token.t) ~(uses : Token.t list) =
  Cursor.report cursor opening.span
    (Trailing_lambda
       {
         receiver =
           (match callee.kind with
           | Member ({ kind = Name receiver; _ }, _) -> Some receiver.text
           | _ -> None);
         call =
           (if Atoms.ends_statement next.kind then
              Some
                {
                  callee_gap = Source.make_span (read_span cursor callee.id).stop opening.span.start;
                  closing = closing.span;
                  uses = List.map (fun (token : Token.t) -> token.span) uses;
                }
            else None);
       })

let integer_type_names =
  [ "Int8"; "Int16"; "Int32"; "Int64"; "UInt8"; "UInt16"; "UInt32"; "UInt64" ]

let rec is_simple_operand (value : Syntax.expression) =
  match value.kind with
  | Name _ | Integer _ | Float _ | Self_value | True | False -> true
  | Member (base, _) -> is_simple_operand base
  | _ -> false

let report_as_conversion cursor ~(value : Syntax.expression) ~(as_token : Token.t)
    ~(target : Syntax.type_expression) =
  let value_span = read_span cursor value.id and target_span = read_span cursor target.id in
  let report conversion =
    Cursor.report cursor as_token.span
      (As_conversion { value = value_span; target = target_span; conversion })
  and report_float float_type =
    Cursor.report cursor as_token.span
      (As_float_conversion
         {
           value = value_span;
           target = target_span;
           float_type;
           is_simple = is_simple_operand value;
         })
  in
  match target.kind with
  | Path_type { path = { modules = []; last }; arguments = []; _ }
    when List.mem last.text integer_type_names ->
      report Integer_conversion
  | Path_type { path = { modules = []; last = { text = "Float32"; _ } }; arguments = []; _ } ->
      report_float Float32
  | Path_type { path = { modules = []; last = { text = "Float64"; _ } }; arguments = []; _ } ->
      report_float Float64
  | Type_error -> Cursor.report cursor as_token.span As_unknown_conversion
  | Path_type _ | Self_type _ | Associated _ | Function_type _ -> report Library_conversion

let report_elif cursor ~(previous_stop : int) ~(elif_token : Token.t) =
  Cursor.report cursor elif_token.span
    (Elif { replaced = Source.make_span previous_stop elif_token.span.stop })

let report_loop cursor ~(loop_token : Token.t) = Cursor.report cursor loop_token.span Loop_keyword

let report_constant_keyword cursor ~(token : Token.t) ~reserved =
  Cursor.report cursor token.span (Constant_keyword { word = Token.spell_reserved reserved })

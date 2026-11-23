let spell_node cursor id = Cursor.spell cursor (Cursor.read_file_span cursor id)

let report cursor code (span : Source.span) message fix_title edits =
  let joins (edit : Source.span Diagnostic.edit) =
    Cursor.joins_neighbors cursor edit.span edit.replacement
  in
  Cursor.report cursor code span message
    ~fixes:(if List.exists joins edits then [] else [ Diagnostic.fix fix_title edits ])

let extend_with_trailing_space (token : Token.t) ~(next : Token.t) =
  Source.make_span token.span.start next.span.start

let increment cursor ~(target : Syntax.expression) ~(operator : Token.t) =
  let replacement, sign =
    match operator.kind with Foreign Plus_plus -> (" += 1", "+") | _ -> (" -= 1", "-")
  in
  let written =
    match spell_node cursor target.id with
    | Some target -> Printf.sprintf "%s %s= 1" target sign
    | None -> Printf.sprintf "%s= 1" sign
  in
  report cursor Increment operator.span
    (Printf.sprintf "Truss has no `%s%s`; write `%s`." sign sign written)
    (Printf.sprintf "Write `%s`" written)
    [ Diagnostic.replace operator.span replacement ]

let report_double_negation cursor ~(operator : Token.t) ~(operand : Syntax.expression) =
  let operand_span = Cursor.read_file_span cursor operand.id in
  report cursor Double_negation operator.span "Truss has no `--`; to negate twice, write `-(-x)`."
    "Write `-(-x)`"
    [
      Diagnostic.replace operator.span "-(-";
      Diagnostic.insert (Source.make_zero_width operand_span.stop) ")";
    ]

let match_arm_comma cursor ~(comma : Token.t) ~(next : Token.t) =
  let is_arm_end =
    next.line_break_before
    || match next.kind with Newline | Punctuation (Close Curly) -> true | _ -> false
  in
  let title, edit =
    if is_arm_end then ("Remove the comma", Diagnostic.delete comma.span)
    else
      ( "Put the next arm on its own line",
        Diagnostic.replace (Source.make_span comma.span.start next.span.start) "\n" )
  in
  report cursor Match_arm_comma comma.span "`match` arms are separated by line breaks, not commas."
    title [ edit ]

let report_conditional cursor ~(condition : Syntax.expression) ~(then_ : Syntax.expression)
    ~(else_ : Syntax.expression) ~(question : Token.t) =
  let condition = Cursor.read_file_span cursor condition.id
  and then_ = Cursor.read_file_span cursor then_.id
  and else_ = Cursor.read_file_span cursor else_.id in
  report cursor Conditional_operator question.span
    "Truss has no conditional operator; write `if x { a } else { b }`." "Write an `if` expression"
    [
      Diagnostic.insert (Source.make_zero_width condition.start) "if ";
      Diagnostic.replace (Source.make_span condition.stop then_.start) " { ";
      Diagnostic.replace (Source.make_span then_.stop else_.start) " } else { ";
      Diagnostic.insert (Source.make_zero_width else_.stop) " }";
    ]

let report_let_mut cursor ~(let_token : Token.t) ~(mut_token : Token.t) =
  report cursor Let_mut mut_token.span "A mutable variable is declared with `var`, not `let mut`."
    "Write `var`"
    [ Diagnostic.replace (Source.make_span let_token.span.start mut_token.span.stop) "var" ]

let report_address_of cursor ~(before : Token.t option) ~(ampersand : Token.t) ~(next : Token.t) =
  let written = match next.kind with Keyword Mut -> "`mut x`" | _ -> "`x`" in
  let separator =
    match before with
    | Some { kind = Upper _ | Lower _ | Keyword _ | Reserved _ | Integer _ | Float _; span; _ }
      when span.stop = ampersand.span.start ->
        " "
    | _ -> ""
  in
  report cursor Address_of ampersand.span
    (Printf.sprintf
       "Truss has no `&`; write %s, with `mut` or `own` before a place only when it is mutated or \
        moved."
       written)
    "Remove the `&`"
    [ Diagnostic.replace (extend_with_trailing_space ampersand ~next) separator ]

let report_closure_bars cursor ~(opening : Token.t) ~(closing : Token.t) ~(body : Syntax.expression)
    ~is_before_else =
  let body_span = Cursor.read_file_span cursor body.id in
  let edits =
    if opening.kind = Punctuation Or_or then
      [ Diagnostic.replace (Source.make_span opening.span.start body_span.start) "fn() " ]
    else
      [
        Diagnostic.replace opening.span "fn(";
        Diagnostic.replace (Source.make_span closing.span.start body_span.start) ") ";
      ]
  in
  let edits =
    match body.kind with
    | Block _ -> edits
    | _ ->
        edits
        @ [
            Diagnostic.insert (Source.make_zero_width body_span.start) "{ ";
            Diagnostic.insert (Source.make_zero_width body_span.stop) " }";
          ]
  in
  let edits =
    if is_before_else then
      (Diagnostic.insert (Source.make_zero_width opening.span.start) "(" :: edits)
      @ [ Diagnostic.insert (Source.make_zero_width body_span.stop) ")" ]
    else edits
  in
  report cursor Closure_bars opening.span "A lambda is written `fn(x) { x + 1 }`."
    "Write `fn(...) { ... }`" edits

let report_brace_record cursor ~(name_stop : int) ~(opening : Token.t) ~(first : Token.t)
    ~(last_stop : int) ~(closing : Token.t) =
  report cursor Brace_record opening.span
    "Records are built with parentheses: `Point(x: 1.0, y: 2.0)`." "Use parentheses"
    [
      Diagnostic.replace (Source.make_span name_stop first.span.start) "(";
      Diagnostic.replace (Source.make_span last_stop closing.span.stop) ")";
    ]

let report_turbofish cursor ~(colons : Token.t) ~(less : Token.t) ~(greater : Token.t) =
  report cursor Turbofish less.span "Type arguments go in square brackets: `parse[Int64](text)`."
    "Use square brackets"
    [
      Diagnostic.replace (Source.make_span colons.span.start less.span.stop) "[";
      Diagnostic.replace greater.span "]";
    ]

let report_angle_brackets cursor ~(angles : Token.t list) =
  report cursor Angle_brackets (List.hd angles).span
    "Type arguments and generic parameters go in square brackets: `List[String]`, `fn \
     first[Element](...)`."
    "Use square brackets"
    (List.map
       (fun (token : Token.t) ->
         Diagnostic.replace token.span
           (match token.kind with
           | Punctuation Less -> "["
           | Punctuation Shift_right -> "]]"
           | _ -> "]"))
       angles)

let report_qualified_variant cursor ~qualifier_start ~(variant : Syntax.name) =
  let variant_start = (Cursor.read_file_span cursor variant.id).start in
  report cursor Qualified_variant
    (Source.make_span qualifier_start variant_start)
    (Printf.sprintf
       "A pattern names a variant alone: `%s`. The type of the scrutinee says which type's variant \
        it is."
       variant.text)
    "Remove the qualifier"
    [ Diagnostic.delete (Source.make_span qualifier_start variant_start) ]

let show_macro_advice = function
  | "println" | "print" | "eprintln" | "eprint" ->
      " Print with `Console.print_line(text)`, and build the text with `${...}` in a string."
  | "format" -> " Build text with `${...}` in a string."
  | "vec" -> " A list is written `[first, second]`."
  | "assert" | "assert_eq" | "assert_ne" | "debug_assert" ->
      " An assertion is a statement, `assert condition`, in a test, a theorem, or a proof."
  | "dbg" -> " `echo value` prints a value while debugging."
  | "panic" -> " Code that cannot be reached is `unreachable`, and a failure is a `Result`."
  | _ -> ""

let report_macro_call cursor ~(name : Syntax.name) ~(bang : Token.t) ~(opening : Token.t) =
  let message =
    Printf.sprintf "Truss has no macros, so `%s!` is not a call.%s" name.text
      (show_macro_advice name.text)
  in
  match (name.text, opening.kind) with
  | "vec", Punctuation (Open Square) ->
      report cursor Macro_call bang.span message "Write a list"
        [
          Diagnostic.delete
            (Source.make_span (Cursor.read_file_span cursor name.id).start bang.span.stop);
        ]
  | _ -> Cursor.report cursor Macro_call bang.span message

let report_keyword_macro cursor ~(bang : Token.t) ~(closing : Token.t) ~has_arguments =
  let message = "Truss has no macros. `todo` and `unreachable` are written without `!()`." in
  if has_arguments then Cursor.report cursor Macro_call bang.span message
  else
    report cursor Macro_call bang.span message "Remove `!()`"
      [ Diagnostic.delete (Source.make_span bang.span.start closing.span.stop) ]

let no_tuples =
  "Parentheses do not make a tuple: every tuple type has a name and named fields. Values that \
   belong together go in a record or a tuple type, such as `core.Pair`, built as `core.Pair(first: \
   a, second: b)`."

let report_tuple cursor ~(opening : Token.t) =
  Cursor.report cursor Tuple opening.span no_tuples;
  raise Cursor.Failed

let report_tuple_field cursor ~(field : Token.t) =
  Cursor.report cursor Tuple field.span
    "A value has no numbered fields. Every field has a name, in a tuple type too, as in \
     `pair.first`.";
  raise Cursor.Failed

let report_power_operator cursor ~(operator : Token.t) =
  Cursor.report cursor Power_operator operator.span
    "Truss has no power operator. Multiply, as in `x * x`, or call the type's own method for a \
     power."

let report_short_declaration cursor ~(target : Syntax.expression) ~(operator : Token.t) =
  let message = "Truss has no `:=`. A new name is declared with `let name = value`." in
  match target.kind with
  | Name _ ->
      report cursor Short_declaration operator.span message "Declare the name with `let`"
        [
          Diagnostic.insert
            (Source.make_zero_width (Cursor.read_file_span cursor target.id).start)
            "let ";
          Diagnostic.replace operator.span "=";
        ]
  | _ -> Cursor.report cursor Short_declaration operator.span message

let pipe_operator cursor ~(value : Syntax.expression) ~(operator : Token.t)
    ~(callee : Syntax.expression) =
  let message = "Truss has no `|>`. A function is called with its argument: `function(value)`." in
  let rec is_path (candidate : Syntax.expression) =
    match candidate.kind with
    | Name _ -> true
    | Member (receiver, _) -> is_path receiver
    | _ -> false
  in
  match if is_path callee then spell_node cursor callee.id else None with
  | Some callee_spelling ->
      let value = Cursor.read_file_span cursor value.id
      and callee = Cursor.read_file_span cursor callee.id in
      report cursor Pipe_operator operator.span message "Write the call"
        [
          Diagnostic.insert (Source.make_zero_width value.start) (callee_spelling ^ "(");
          Diagnostic.replace (Source.make_span value.stop callee.stop) ")";
        ]
  | None -> Cursor.report cursor Pipe_operator operator.span message

let report_lambda_annotation cursor ~from ~stop =
  report cursor Lambda_annotation (Source.make_span from stop)
    "A lambda's parameters and result have no annotations. Their types are inferred from where the \
     lambda is passed."
    "Remove the annotation"
    [ Diagnostic.delete (Source.make_span from stop) ]

let report_impl_parameters cursor ~(opening : Token.t) ~(closing : Token.t) ~has_bounds =
  let message =
    "An `impl` has no parameters of its own. The type after `for` declares them, with their \
     bounds: `impl Trait for Box[Item: Ordered]`."
  in
  let span = Source.make_span opening.span.start closing.span.stop in
  if has_bounds then Cursor.report cursor Impl_parameters opening.span message
  else
    report cursor Impl_parameters opening.span message "Remove the parameters"
      [ Diagnostic.delete span ]

let report_null_coalescing cursor ~(value : Syntax.expression) ~(first : Token.t)
    ~(second : Token.t) ~(default : Syntax.expression) =
  let value_span = Cursor.read_file_span cursor value.id
  and default_span = Cursor.read_file_span cursor default.id in
  let needs_parentheses =
    match value.kind with
    | Binary _ | Is _ | Range _ | Prefix _ | Mode _ | Quantified _ | Echo _ | Return _ -> true
    | _ -> false
  in
  report cursor Null_coalescing first.span
    (Printf.sprintf
       "Truss has no `%s`. An `Option`'s value, or a default when it has none, is \
        `option.unwrap_or(default)`."
       (match second.kind with Punctuation Colon -> "?:" | _ -> "??"))
    "Call `unwrap_or`"
    ((if needs_parentheses then [ Diagnostic.insert (Source.make_zero_width value_span.start) "(" ]
      else [])
    @ [
        Diagnostic.replace
          (Source.make_span value_span.stop default_span.start)
          (if needs_parentheses then ").unwrap_or(" else ".unwrap_or(");
        Diagnostic.insert (Source.make_zero_width default_span.stop) ")";
      ])

let singularize word =
  let length = String.length word in
  let ends suffix = String.ends_with ~suffix word in
  if length > 3 && ends "ies" then Some (String.sub word 0 (length - 3) ^ "y")
  else if
    length > 1 && ends "s"
    && not (List.exists ends [ "ss"; "us"; "is"; "ses"; "xes"; "zes"; "ches"; "shes" ])
  then Some (String.sub word 0 (length - 1))
  else None

let derive_parameter_name (callee : Syntax.expression) =
  let receiver = match callee.kind with Member (receiver, _) -> Some receiver | _ -> None in
  let candidate =
    match receiver with Some { kind = Name last; _ } -> singularize last.text | _ -> None
  in
  match candidate with
  | Some name when name <> "it" && Token.find_word name = None -> name
  | _ -> "element"

let report_trailing_lambda cursor ~(callee : Syntax.expression) ~parameter ~(opening : Token.t)
    ~(closing : Token.t) ~(next : Token.t) ~(uses : Token.t list) =
  let message =
    Printf.sprintf
      "A lambda is passed inside the parentheses, with a named parameter: `fn(%s) { ... }`."
      parameter
  in
  if Atoms.ends_statement next.kind then
    let callee_stop = (Cursor.read_file_span cursor callee.id).stop in
    report cursor Trailing_lambda opening.span message "Pass a lambda"
      (Diagnostic.replace
         (Source.make_span callee_stop opening.span.start)
         (Printf.sprintf "(fn(%s) " parameter)
      :: Diagnostic.insert (Source.make_zero_width closing.span.stop) ")"
      :: List.map (fun (token : Token.t) -> Diagnostic.replace token.span parameter) uses)
  else Cursor.report cursor Trailing_lambda opening.span message

let integer_type_names =
  [ "Int8"; "Int16"; "Int32"; "Int64"; "UInt8"; "UInt16"; "UInt32"; "UInt64" ]

let report_as_conversion cursor ~(value : Syntax.expression) ~(as_token : Token.t)
    ~(target : Syntax.type_expression) =
  match spell_node cursor target.id with
  | Some target_spelling ->
      let value = Cursor.read_file_span cursor value.id
      and target = Cursor.read_file_span cursor target.id in
      let make_conversion_fix name =
        Diagnostic.fix
          (Printf.sprintf "Write `%s.%s(...)`" target_spelling name)
          [
            Diagnostic.insert
              (Source.make_zero_width value.start)
              (Printf.sprintf "%s.%s(" target_spelling name);
            Diagnostic.replace (Source.make_span value.stop target.stop) ")";
          ]
      in
      let report_with_names checked fallible =
        Cursor.report cursor As_conversion as_token.span
          (Printf.sprintf
             "Truss has no `as`; write `%s.%s(x)`, or `%s.%s(x)` when the value may not fit."
             target_spelling checked target_spelling fallible)
          ~fixes:[ make_conversion_fix checked; make_conversion_fix fallible ]
      in
      if List.mem target_spelling integer_type_names then
        report_with_names "from_integer" "try_from_integer"
      else if List.mem target_spelling [ "Float32"; "Float64" ] then
        let method_ = "to_" ^ String.lowercase_ascii target_spelling in
        let is_simple =
          match Cursor.spell cursor value with
          | Some value_text ->
              String.for_all
                (fun character ->
                  character = '_' || character = '.'
                  || (character >= 'a' && character <= 'z')
                  || (character >= 'A' && character <= 'Z')
                  || (character >= '0' && character <= '9'))
                value_text
          | None -> false
        in
        Cursor.report cursor As_conversion as_token.span
          (Printf.sprintf "Truss has no `as`; write `x.%s()`." method_)
          ~fixes:
            [
              Diagnostic.fix
                (Printf.sprintf "Write `.%s()`" method_)
                ((if is_simple then []
                  else [ Diagnostic.insert (Source.make_zero_width value.start) "(" ])
                @ [
                    Diagnostic.replace
                      (Source.make_span value.stop target.stop)
                      ((if is_simple then "" else ")") ^ "." ^ method_ ^ "()");
                  ]);
            ]
      else report_with_names "from" "try_from"
  | None ->
      Cursor.report cursor As_conversion as_token.span
        "Truss has no `as`; call a conversion of the target type, such as `from_integer` or \
         `try_from_integer` for an integer, or `from` or `try_from` for a library type."

let report_elif cursor ~(previous_stop : int) ~(elif_token : Token.t) =
  report cursor Elif elif_token.span "Truss writes `else if`, not `elif`." "Write `else if`"
    [ Diagnostic.replace (Source.make_span previous_stop elif_token.span.stop) " else if" ]

let report_loop cursor ~(loop_token : Token.t) =
  report cursor Reserved_word loop_token.span "Truss has no `loop`; write `while true`."
    "Write `while true`"
    [ Diagnostic.replace loop_token.span "while true" ]

let report_constant_keyword cursor ~(token : Token.t) ~reserved =
  let word = Token.spell_reserved reserved in
  report cursor Reserved_word token.span
    (Printf.sprintf "Truss has no `%s`; a constant is a `let` at the top level." word)
    "Write `let`"
    [ Diagnostic.replace token.span "let" ]

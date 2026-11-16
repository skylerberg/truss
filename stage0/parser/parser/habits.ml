open Syntax

let node_spelling cursor id = Cursor.spelling cursor (Cursor.read_file_span cursor id)

let report cursor code (span : Source.span) message fix_title edits =
  let joins (edit : Source.span Diagnostic.edit) =
    Cursor.joins_neighbors cursor edit.span edit.replacement
  in
  Cursor.report cursor code span message
    ~fixes:(if List.exists joins edits then [] else [ Diagnostic.fix fix_title edits ])

let token_with_trailing_space (token : Token.t) ~(next : Token.t) =
  Source.span token.span.start next.span.start

let increment cursor ~(target : expression) ~(operator : Token.t) =
  let replacement, sign =
    match operator.kind with Foreign Plus_plus -> (" += 1", "+") | _ -> (" -= 1", "-")
  in
  let written =
    match node_spelling cursor target.id with
    | Some target -> Printf.sprintf "%s %s= 1" target sign
    | None -> Printf.sprintf "%s= 1" sign
  in
  report cursor Increment operator.span
    (Printf.sprintf "Truss has no `%s%s`; write `%s`." sign sign written)
    (Printf.sprintf "Write `%s`" written)
    [ Diagnostic.replace operator.span replacement ]

let double_negation cursor ~(operator : Token.t) ~(operand : expression) =
  let operand_span = Cursor.read_file_span cursor operand.id in
  report cursor Double_negation operator.span "Truss has no `--`; to negate twice, write `-(-x)`."
    "Write `-(-x)`"
    [
      Diagnostic.replace operator.span "-(-";
      Diagnostic.insert (Source.zero_width operand_span.stop) ")";
    ]

let match_arm_comma cursor ~(comma : Token.t) =
  report cursor Match_arm_comma comma.span "`match` arms are separated by line breaks, not commas."
    "Remove the comma"
    [ Diagnostic.delete comma.span ]

let conditional cursor ~(condition : expression) ~(then_ : expression) ~(else_ : expression)
    ~(question : Token.t) =
  let condition = Cursor.read_file_span cursor condition.id
  and then_ = Cursor.read_file_span cursor then_.id
  and else_ = Cursor.read_file_span cursor else_.id in
  report cursor Conditional_operator question.span
    "Truss has no conditional operator; write `if x { a } else { b }`." "Write an `if` expression"
    [
      Diagnostic.insert (Source.zero_width condition.start) "if ";
      Diagnostic.replace (Source.span condition.stop then_.start) " { ";
      Diagnostic.replace (Source.span then_.stop else_.start) " } else { ";
      Diagnostic.insert (Source.zero_width else_.stop) " }";
    ]

let let_mut cursor ~(let_token : Token.t) ~(mut_token : Token.t) =
  report cursor Let_mut mut_token.span "A mutable variable is declared with `var`, not `let mut`."
    "Write `var`"
    [ Diagnostic.replace (Source.span let_token.span.start mut_token.span.stop) "var" ]

let address_of cursor ~(before : Token.t option) ~(ampersand : Token.t) ~(next : Token.t) =
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
    [ Diagnostic.replace (token_with_trailing_space ampersand ~next) separator ]

let closure_bars cursor ~(opening : Token.t) ~(closing : Token.t) ~(body : expression)
    ~is_before_else =
  let body_span = Cursor.read_file_span cursor body.id in
  let edits =
    if opening.kind = Punctuation Or_or then
      [ Diagnostic.replace (Source.span opening.span.start body_span.start) "fn() " ]
    else
      [
        Diagnostic.replace opening.span "fn(";
        Diagnostic.replace (Source.span closing.span.start body_span.start) ") ";
      ]
  in
  let edits =
    match body.kind with
    | Block _ -> edits
    | _ ->
        edits
        @ [
            Diagnostic.insert (Source.zero_width body_span.start) "{ ";
            Diagnostic.insert (Source.zero_width body_span.stop) " }";
          ]
  in
  let edits =
    if is_before_else then
      (Diagnostic.insert (Source.zero_width opening.span.start) "(" :: edits)
      @ [ Diagnostic.insert (Source.zero_width body_span.stop) ")" ]
    else edits
  in
  report cursor Closure_bars opening.span "A lambda is written `fn(x) { x + 1 }`."
    "Write `fn(...) { ... }`" edits

let brace_record cursor ~(name_stop : int) ~(opening : Token.t) ~(first : Token.t)
    ~(last_stop : int) ~(closing : Token.t) =
  report cursor Brace_record opening.span
    "Records are built with parentheses: `Point(x: 1.0, y: 2.0)`." "Use parentheses"
    [
      Diagnostic.replace (Source.span name_stop first.span.start) "(";
      Diagnostic.replace (Source.span last_stop closing.span.stop) ")";
    ]

let turbofish cursor ~(colons : Token.t) ~(less : Token.t) ~(greater : Token.t) =
  report cursor Turbofish less.span "Type arguments go in square brackets: `parse[Int64](text)`."
    "Use square brackets"
    [
      Diagnostic.replace (Source.span colons.span.start less.span.stop) "[";
      Diagnostic.replace greater.span "]";
    ]

let angle_brackets cursor ~(angles : Token.t list) =
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

let path_separator cursor ~(separator : Token.t) =
  report cursor Path_separator separator.span
    "`::` follows only the name of a module. A variant, a constant, or a function of a type is \
     named with `.`, as in `Shape.Circle`."
    "Write `.`"
    [ Diagnostic.replace separator.span "." ]

let qualified_variant cursor ~qualifier_start ~(variant : name) =
  let variant_start = (Cursor.read_file_span cursor variant.id).start in
  report cursor Qualified_variant
    (Source.span qualifier_start variant_start)
    (Printf.sprintf
       "A pattern names a variant alone: `%s`. The type of the scrutinee says which type's variant \
        it is."
       variant.text)
    "Remove the qualifier"
    [ Diagnostic.delete (Source.span qualifier_start variant_start) ]

let macro_advice = function
  | "println" | "print" | "eprintln" | "eprint" ->
      " Print with `Console.print_line(text)`, and build the text with `${...}` in a string."
  | "format" -> " Build text with `${...}` in a string."
  | "vec" -> " A list is written `[first, second]`."
  | "assert" | "assert_eq" | "assert_ne" | "debug_assert" ->
      " An assertion is a statement, `assert condition`, in a test, a theorem, or a proof."
  | "dbg" -> " `echo value` prints a value while debugging."
  | "panic" -> " Code that cannot be reached is `unreachable`, and a failure is a `Result`."
  | _ -> ""

let macro_call cursor ~(name : name) ~(bang : Token.t) ~(opening : Token.t) =
  let message =
    Printf.sprintf "Truss has no macros, so `%s!` is not a call.%s" name.text
      (macro_advice name.text)
  in
  match (name.text, opening.kind) with
  | "vec", Punctuation (Open Square) ->
      report cursor Macro_call bang.span message "Write a list"
        [
          Diagnostic.delete
            (Source.span (Cursor.read_file_span cursor name.id).start bang.span.stop);
        ]
  | _ -> Cursor.report cursor Macro_call bang.span message

let keyword_macro cursor ~(bang : Token.t) ~(closing : Token.t) ~has_arguments =
  let message = "Truss has no macros. `todo` and `unreachable` are written without `!()`." in
  if has_arguments then Cursor.report cursor Macro_call bang.span message
  else
    report cursor Macro_call bang.span message "Remove `!()`"
      [ Diagnostic.delete (Source.span bang.span.start closing.span.stop) ]

let no_tuples =
  "Truss has no tuples. Values that belong together go in a record, whose fields have names, such \
   as `Pair(first: a, second: b)`."

let tuple cursor ~(opening : Token.t) =
  Cursor.report cursor Tuple opening.span no_tuples;
  raise Cursor.Failed

let tuple_field cursor ~(field : Token.t) =
  Cursor.report cursor Tuple field.span
    "Truss has no tuples, so a value has no numbered fields. A record's fields have names, as in \
     `pair.first`.";
  raise Cursor.Failed

let power_operator cursor ~(operator : Token.t) =
  Cursor.report cursor Power_operator operator.span
    "Truss has no power operator. Multiply, as in `x * x`, or call the type's own method for a \
     power."

let short_declaration cursor ~(target : expression) ~(operator : Token.t) =
  let message = "Truss has no `:=`. A new name is declared with `let name = value`." in
  match target.kind with
  | Name { modules = []; _ } ->
      report cursor Short_declaration operator.span message "Declare the name with `let`"
        [
          Diagnostic.insert
            (Source.zero_width (Cursor.read_file_span cursor target.id).start)
            "let ";
          Diagnostic.replace operator.span "=";
        ]
  | _ -> Cursor.report cursor Short_declaration operator.span message

let pipe_operator cursor ~(value : expression) ~(operator : Token.t) ~(callee : expression) =
  let message = "Truss has no `|>`. A function is called with its argument: `function(value)`." in
  let rec is_path (candidate : expression) =
    match candidate.kind with
    | Name _ -> true
    | Member (receiver, _) -> is_path receiver
    | _ -> false
  in
  match if is_path callee then node_spelling cursor callee.id else None with
  | Some callee_spelling ->
      let value = Cursor.read_file_span cursor value.id
      and callee = Cursor.read_file_span cursor callee.id in
      report cursor Pipe_operator operator.span message "Write the call"
        [
          Diagnostic.insert (Source.zero_width value.start) (callee_spelling ^ "(");
          Diagnostic.replace (Source.span value.stop callee.stop) ")";
        ]
  | None -> Cursor.report cursor Pipe_operator operator.span message

let lambda_annotation cursor ~from ~stop =
  report cursor Lambda_annotation (Source.span from stop)
    "A lambda's parameters and result have no annotations. Their types are inferred from where the \
     lambda is passed."
    "Remove the annotation"
    [ Diagnostic.delete (Source.span from stop) ]

let impl_parameters cursor ~(opening : Token.t) ~(closing : Token.t) ~has_bounds =
  let message =
    "An `impl` has no parameters of its own. The type after `for` declares them, with their \
     bounds: `impl Trait for Box[Item: Ordered]`."
  in
  let span = Source.span opening.span.start closing.span.stop in
  if has_bounds then Cursor.report cursor Impl_parameters opening.span message
  else
    report cursor Impl_parameters opening.span message "Remove the parameters"
      [ Diagnostic.delete span ]

let null_coalescing cursor ~(value : expression) ~(first : Token.t) ~(second : Token.t)
    ~(default : expression) =
  let value_span = Cursor.read_file_span cursor value.id
  and default_span = Cursor.read_file_span cursor default.id in
  let needs_parentheses =
    match value.kind with
    | Binary _ | Is _ | Range _ | Prefix _ | Mode _ | Any _ | Quantified _ | Echo _ | Return _ ->
        true
    | _ -> false
  in
  report cursor Null_coalescing first.span
    (Printf.sprintf
       "Truss has no `%s`. An `Option`'s value, or a default when it has none, is \
        `option.unwrap_or(default)`."
       (match second.kind with Punctuation Colon -> "?:" | _ -> "??"))
    "Call `unwrap_or`"
    ((if needs_parentheses then [ Diagnostic.insert (Source.zero_width value_span.start) "(" ]
      else [])
    @ [
        Diagnostic.replace
          (Source.span value_span.stop default_span.start)
          (if needs_parentheses then ").unwrap_or(" else ".unwrap_or(");
        Diagnostic.insert (Source.zero_width default_span.stop) ")";
      ])

let singular word =
  let length = String.length word in
  let ends suffix = String.ends_with ~suffix word in
  if length > 3 && ends "ies" then Some (String.sub word 0 (length - 3) ^ "y")
  else if
    length > 1 && ends "s"
    && not (List.exists ends [ "ss"; "us"; "is"; "ses"; "xes"; "zes"; "ches"; "shes" ])
  then Some (String.sub word 0 (length - 1))
  else None

let parameter_name (callee : expression) =
  let receiver = match callee.kind with Member (receiver, _) -> Some receiver | _ -> None in
  let candidate =
    match receiver with
    | Some { kind = Name { modules = []; last }; _ } -> singular last.text
    | _ -> None
  in
  match candidate with
  | Some name when name <> "it" && Token.word name = None -> name
  | _ -> "element"

let trailing_lambda cursor ~(callee : expression) ~parameter ~(opening : Token.t)
    ~(closing : Token.t) ~(uses : Token.t list) =
  let callee_stop = (Cursor.read_file_span cursor callee.id).stop in
  report cursor Trailing_lambda opening.span
    (Printf.sprintf
       "A lambda is passed inside the parentheses, with a named parameter: `fn(%s) { ... }`."
       parameter)
    "Pass a lambda"
    (Diagnostic.replace
       (Source.span callee_stop opening.span.start)
       (Printf.sprintf "(fn(%s) " parameter)
    :: Diagnostic.insert (Source.zero_width closing.span.stop) ")"
    :: List.map (fun (token : Token.t) -> Diagnostic.replace token.span parameter) uses)

let as_conversion cursor ~(value : expression) ~(as_token : Token.t) ~(target : type_expression) =
  match node_spelling cursor target.id with
  | Some target_spelling ->
      let value = Cursor.read_file_span cursor value.id
      and target = Cursor.read_file_span cursor target.id in
      let conversion name =
        Diagnostic.fix
          (Printf.sprintf "Write `%s.%s(...)`" target_spelling name)
          [
            Diagnostic.insert (Source.zero_width value.start)
              (Printf.sprintf "%s.%s(" target_spelling name);
            Diagnostic.replace (Source.span value.stop target.stop) ")";
          ]
      in
      Cursor.report cursor As_conversion as_token.span
        (Printf.sprintf
           "Truss has no `as`; write `%s.from(x)`, or `%s.try_from(x)` when the conversion can \
            lose information."
           target_spelling target_spelling)
        ~fixes:[ conversion "from"; conversion "try_from" ]
  | None ->
      Cursor.report cursor As_conversion as_token.span
        "Truss has no `as`; call the target type's `from`, or its `try_from` when the conversion \
         can lose information."

let elif cursor ~(previous_stop : int) ~(elif_token : Token.t) =
  report cursor Elif elif_token.span "Truss writes `else if`, not `elif`." "Write `else if`"
    [ Diagnostic.replace (Source.span previous_stop elif_token.span.stop) " else if" ]

let loop cursor ~(loop_token : Token.t) =
  report cursor Reserved_word loop_token.span "Truss has no `loop`; write `while true`."
    "Write `while true`"
    [ Diagnostic.replace loop_token.span "while true" ]

let constant_keyword cursor ~(token : Token.t) ~reserved =
  let word = Token.reserved_spelling reserved in
  report cursor Reserved_word token.span
    (Printf.sprintf "Truss has no `%s`; a constant is a `let` at the top level." word)
    "Write `let`"
    [ Diagnostic.replace token.span "let" ]

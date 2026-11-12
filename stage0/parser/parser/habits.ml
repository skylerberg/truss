(* Syntax from other languages that is made of valid tokens: the message and
   exact fix for each.

   The parsing modules recognize each habit at the point where the ordinary
   grammar has already rejected a token, so a recognizer can never change
   what valid code means, and call the function here that reports it. Each
   fix is exact: applying it leaves the code the author meant. *)

open Syntax

let text cursor (span : Source.span) = Cursor.text cursor span
let node_text cursor span = text cursor (Cursor.absolute cursor span)

let report cursor code (span : Source.span) message fix_title edits =
  Cursor.report cursor code span message ~fixes:[ Diagnostic.fix fix_title edits ]

(* The bytes from the end of one token to the start of the next, so that a
   fix can remove a token together with the space after it. *)
let through_next (token : Token.t) (next : Token.t) = Source.span token.span.start next.span.start

(* [i++] and [i--]. *)
let increment cursor ~(target : expression) ~(operator : Token.t) =
  let replacement, sign =
    match operator.kind with Foreign Plus_plus -> (" += 1", "+") | _ -> (" -= 1", "-")
  in
  let target_text = node_text cursor target.span in
  report cursor Increment operator.span
    (Printf.sprintf "Truss has no `%s%s`; write `%s %s= 1`." sign sign target_text sign)
    (Printf.sprintf "Write `%s %s= 1`" target_text sign)
    [ Diagnostic.replace operator.span replacement ]

(* [--x], which Truss rejects rather than reading as two negations. *)
let double_negation cursor ~(operator : Token.t) ~(operand : expression) =
  let operand_span = Cursor.absolute cursor operand.span in
  report cursor Double_negation operator.span "Truss has no `--`; to negate twice, write `-(-x)`."
    "Write `-(-x)`"
    [
      Diagnostic.replace operator.span "-(-";
      Diagnostic.insert (Source.zero_width operand_span.stop) ")";
    ]

(* [A => 1,]: arms are separated by line breaks. *)
let match_arm_comma cursor ~(comma : Token.t) =
  report cursor Match_arm_comma comma.span "`match` arms are separated by line breaks, not commas."
    "Remove the comma"
    [ Diagnostic.delete comma.span ]

(* [x ? a : b]. *)
let conditional cursor ~(condition : expression) ~(then_ : expression) ~(else_ : expression)
    ~(question : Token.t) =
  let whole =
    Source.span (Cursor.absolute cursor condition.span).start
      (Cursor.absolute cursor else_.span).stop
  in
  report cursor Conditional_operator question.span
    "Truss has no conditional operator; write `if x { a } else { b }`." "Write an `if` expression"
    [
      Diagnostic.replace whole
        (Printf.sprintf "if %s { %s } else { %s }" (node_text cursor condition.span)
           (node_text cursor then_.span) (node_text cursor else_.span));
    ]

(* [let mut x]. *)
let let_mut cursor ~(let_token : Token.t) ~(mut_token : Token.t) =
  report cursor Let_mut mut_token.span
    "A variable that can change is declared with `var`, not `let mut`." "Write `var`"
    [ Diagnostic.replace (Source.span let_token.span.start mut_token.span.stop) "var" ]

(* [&x] and [&mut x]: arguments are marked with [mut] or [own], never [&]. *)
let address_of cursor ~(before : Token.t option) ~(ampersand : Token.t) ~(next : Token.t) =
  let marked = match next.kind with Keyword Mut -> "`mut x`" | _ -> "`x`" in
  (* Between two words, as in [match& x], a space keeps them separate tokens. *)
  let separator =
    match before with
    | Some { kind = Upper _ | Lower _ | Keyword _ | Reserved _ | Integer _ | Float _; span; _ }
      when span.stop = ampersand.span.start ->
        " "
    | _ -> ""
  in
  report cursor Address_of ampersand.span
    (Printf.sprintf
       "Truss has no `&`; write %s, marking a place with `mut` or `own` only when it is changed or \
        moved."
       marked)
    "Remove the `&`"
    [ Diagnostic.replace (through_next ampersand next) separator ]

(* [|x| x + 1] and [|| x]. *)
let closure_bars cursor ~(opening : Token.t) ~(closing : Token.t) ~(body : expression) ~before_else
    =
  let body_span = Cursor.absolute cursor body.span in
  let edits =
    if opening.kind = Punctuation Or_or then
      (* [||], one token. *)
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
  (* Before the [else] of a [let ... else], an expression cannot end with
     the lambda's [}]. *)
  let edits =
    if before_else then
      (Diagnostic.insert (Source.zero_width opening.span.start) "(" :: edits)
      @ [ Diagnostic.insert (Source.zero_width body_span.stop) ")" ]
    else edits
  in
  report cursor Closure_bars opening.span "A lambda is written `fn(x) { x + 1 }`."
    "Write `fn(...) { ... }`" edits

(* [Point { x: 1.0 }]: records are built with parentheses. *)
let brace_record cursor ~(name_stop : int) ~(opening : Token.t) ~(first : Token.t)
    ~(last_stop : int) ~(closing : Token.t) =
  report cursor Brace_record opening.span
    "Records are built with parentheses: `Point(x: 1.0, y: 2.0)`." "Use parentheses"
    [
      Diagnostic.replace (Source.span name_stop first.span.start) "(";
      Diagnostic.replace (Source.span last_stop closing.span.stop) ")";
    ]

(* [parse::<Int64>(text)]. *)
let turbofish cursor ~(colons : Token.t) ~(less : Token.t) ~(greater : Token.t) =
  report cursor Turbofish less.span "Type arguments go in square brackets: `parse[Int64](text)`."
    "Use square brackets"
    [
      Diagnostic.replace (Source.span colons.span.start less.span.stop) "[";
      Diagnostic.replace greater.span "]";
    ]

(* [List<String>] and [fn first<T>]. [angles] are the [<], [>], and [>>]
   tokens. *)
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

(* [Shape::Circle] and [Vec::new]: [::] follows only a module's name. *)
let path_separator cursor ~(separator : Token.t) =
  report cursor Path_separator separator.span
    "`::` follows only the name of a module. A variant, a constant, or a function of a type is \
     named with `.`, as in `Shape.Circle`."
    "Write `.`"
    [ Diagnostic.replace separator.span "." ]

(* [Shape.Circle(radius)] and [Shape::Circle(radius)] in a pattern, where
   the qualifier runs from [qualifier_start] to the variant's name. *)
let qualified_variant cursor ~qualifier_start ~(variant : Token.t) =
  report cursor Qualified_variant
    (Source.span qualifier_start variant.span.start)
    (Printf.sprintf
       "A pattern names a variant without its type: `%s`. The type of the scrutinee says which \
        type's variant it is."
       (Cursor.text cursor variant.span))
    "Remove the type"
    [ Diagnostic.delete (Source.span qualifier_start variant.span.start) ]

(* What to write in place of a macro of another language, by its name. *)
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

(* [println!(...)] and [vec![...]]. Only [vec![...]] has an exact fix. *)
let macro_call cursor ~(name : name) ~(bang : Token.t) ~(opening : Token.t) =
  let message =
    Printf.sprintf "Truss has no macros, so `%s!` is not a call.%s" name.text
      (macro_advice name.text)
  in
  match (name.text, opening.kind) with
  | "vec", Punctuation (Open Square) ->
      report cursor Macro_call bang.span message "Write a list"
        [ Diagnostic.delete (Source.span (Cursor.absolute cursor name.span).start bang.span.stop) ]
  | _ -> Cursor.report cursor Macro_call bang.span message

(* [todo!()] and [unreachable!()]: the keyword alone is the expression. With
   arguments, removing them would lose what they say, so there is no fix. *)
let keyword_macro cursor ~(bang : Token.t) ~(closing : Token.t) ~empty =
  let message = "Truss has no macros. `todo` and `unreachable` are written without `!()`." in
  if empty then
    report cursor Macro_call bang.span message "Remove `!()`"
      [ Diagnostic.delete (Source.span bang.span.start closing.span.stop) ]
  else Cursor.report cursor Macro_call bang.span message

let no_tuples =
  "Truss has no tuples. Values that belong together go in a record, whose fields have names, such \
   as `Pair(first: a, second: b)`."

(* [(a, b)] as an expression, and [(Int64, String)] as a type. *)
let tuple cursor ~(opening : Token.t) =
  Cursor.report cursor Tuple opening.span no_tuples;
  raise Cursor.Failed

(* [pair.0]. *)
let tuple_field cursor ~(field : Token.t) =
  Cursor.report cursor Tuple field.span
    "Truss has no tuples, so a value has no numbered fields. A record's fields have names, as in \
     `pair.first`.";
  raise Cursor.Failed

(* [a ** b]. *)
let power_operator cursor ~(operator : Token.t) =
  Cursor.report cursor Power_operator operator.span
    "Truss has no power operator. Multiply, as in `x * x`, or call the type's own method for a \
     power."

(* [name := value], from Go, and [target := value] with any other target. *)
let short_declaration cursor ~(target : expression) ~(operator : Token.t) =
  let message = "Truss has no `:=`. A new name is declared with `let name = value`." in
  match target.kind with
  | Name { modules = []; _ } ->
      report cursor Short_declaration operator.span message "Declare the name with `let`"
        [
          Diagnostic.insert (Source.zero_width (Cursor.absolute cursor target.span).start) "let ";
          Diagnostic.replace operator.span "=";
        ]
  | _ -> Cursor.report cursor Short_declaration operator.span message

(* [value |> function]. The fix is exact only when the right operand is a
   name or a member, since the languages with [|>] disagree about which
   argument of a call the value becomes. *)
let pipe_operator cursor ~(value : expression) ~(operator : Token.t) ~(callee : expression) =
  let message = "Truss has no `|>`. A function is called with its argument: `function(value)`." in
  let rec is_path (candidate : expression) =
    match candidate.kind with
    | Name _ -> true
    | Member (receiver, _) -> is_path receiver
    | _ -> false
  in
  if is_path callee then
    report cursor Pipe_operator operator.span message "Write the call"
      [
        Diagnostic.replace
          (Source.span (Cursor.absolute cursor value.span).start
             (Cursor.absolute cursor callee.span).stop)
          (Printf.sprintf "%s(%s)" (node_text cursor callee.span) (node_text cursor value.span));
      ]
  else Cursor.report cursor Pipe_operator operator.span message

(* [fn(x: Int64) -> Int64 { ... }]: the annotation from [from] to [stop]. *)
let lambda_annotation cursor ~from ~stop =
  report cursor Lambda_annotation (Source.span from stop)
    "A lambda's parameters and result have no annotations. Their types are inferred from where the \
     lambda is passed."
    "Remove the annotation"
    [ Diagnostic.delete (Source.span from stop) ]

(* [impl<T> Trait for Box<T>], from Rust. [plain] says that the parameters
   are names alone, with no bounds, so that removing them loses nothing. *)
let impl_parameters cursor ~(opening : Token.t) ~(closing : Token.t) ~plain =
  let message =
    "An `impl` has no parameters of its own. The type after `for` declares them, with their \
     bounds: `impl Trait for Box[Item: Ordered]`."
  in
  let span = Source.span opening.span.start closing.span.stop in
  if plain then
    report cursor Impl_parameters opening.span message "Remove the parameters"
      [ Diagnostic.delete span ]
  else Cursor.report cursor Impl_parameters opening.span message

(* [a ?? b] and [a ?: b]. *)
let null_coalescing cursor ~(value : expression) ~(first : Token.t) ~(second : Token.t)
    ~(default : expression) =
  let value_span = Cursor.absolute cursor value.span
  and default_span = Cursor.absolute cursor default.span in
  (* A method call binds tighter than every operator, so an operand that is
     an operation goes in parentheses. *)
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
       (Cursor.text cursor (Source.span first.span.start second.span.stop)))
    "Call `unwrap_or`"
    ((if needs_parentheses then [ Diagnostic.insert (Source.zero_width value_span.start) "(" ]
      else [])
    @ [
        Diagnostic.replace
          (Source.span value_span.stop default_span.start)
          (if needs_parentheses then ").unwrap_or(" else ".unwrap_or(");
        Diagnostic.insert (Source.zero_width default_span.stop) ")";
      ])

(* The singular of a plural English noun whose plural is regular: [items]
   and [entries], but not [statuses] or [classes]. *)
let singular word =
  let length = String.length word in
  let ends suffix = String.ends_with ~suffix word in
  if length > 3 && ends "ies" then Some (String.sub word 0 (length - 3) ^ "y")
  else if
    length > 1 && ends "s"
    && not (List.exists ends [ "ss"; "us"; "is"; "ses"; "xes"; "zes"; "ches"; "shes" ])
  then Some (String.sub word 0 (length - 1))
  else None

(* The name a lambda's parameter gets in place of [it]: the singular of the
   collection's name, as in [items.map(fn(item) { item.name })], when
   [singular] can derive it, and otherwise [element]. *)
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

(* [items.map { it.name }]: a lambda goes inside the parentheses. *)
let trailing_lambda cursor ~(callee : expression) ~parameter ~(opening : Token.t)
    ~(closing : Token.t) ~(uses : Token.t list) =
  let callee_stop = (Cursor.absolute cursor callee.span).stop in
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

(* [x as Int64]. *)
let as_conversion cursor ~(value : expression) ~(as_token : Token.t) ~(target : type_expression) =
  let whole =
    Source.span (Cursor.absolute cursor value.span).start (Cursor.absolute cursor target.span).stop
  in
  let target_text = node_text cursor target.span and value_text = node_text cursor value.span in
  (* [from] for a conversion that cannot lose information, and [try_from],
     which returns a [Result], for one that can, as most casts written with
     [as] are. Which one the author meant depends on the types. *)
  let conversion name =
    Diagnostic.fix
      (Printf.sprintf "Write `%s.%s(...)`" target_text name)
      [ Diagnostic.replace whole (Printf.sprintf "%s.%s(%s)" target_text name value_text) ]
  in
  Cursor.report cursor As_conversion as_token.span
    (Printf.sprintf
       "Truss has no `as`; write `%s.from(x)`, or `%s.try_from(x)` when the conversion can lose \
        information."
       target_text target_text)
    ~fixes:[ conversion "from"; conversion "try_from" ]

(* [elif]: written after the [}] that ends an [if]. *)
let elif cursor ~(previous_stop : int) ~(elif_token : Token.t) =
  report cursor Elif elif_token.span "Truss writes `else if`, not `elif`." "Write `else if`"
    [ Diagnostic.replace (Source.span previous_stop elif_token.span.stop) " else if" ]

(* [loop {]. *)
let loop cursor ~(loop_token : Token.t) =
  report cursor Reserved_word loop_token.span "Truss has no `loop`; write `while true`."
    "Write `while true`"
    [ Diagnostic.replace loop_token.span "while true" ]

(* [const] and [static] before a constant. *)
let constant_keyword cursor ~(token : Token.t) =
  let word = Cursor.text cursor token.span in
  report cursor Reserved_word token.span
    (Printf.sprintf "Truss has no `%s`; a constant is a `let` at the top level." word)
    "Write `let`"
    [ Diagnostic.replace token.span "let" ]

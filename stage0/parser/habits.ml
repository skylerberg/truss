(* Syntax from other languages that is made of valid tokens: the message and
   exact fix for each. See PARSER.md, "Syntax from other languages".

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
    (Printf.sprintf "Truss has no `%s%s`; write `%s %s= 1`" sign sign target_text sign)
    (Printf.sprintf "Write `%s %s= 1`" target_text sign)
    [ Diagnostic.replace operator.span replacement ]

(* [--x], which Truss rejects rather than reading as two negations. *)
let double_negation cursor ~(operator : Token.t) ~(operand : expression) =
  let operand_span = Cursor.absolute cursor operand.span in
  report cursor Double_negation operator.span "Truss has no `--`; to negate twice, write `-(-x)`"
    "Write `-(-x)`"
    [ Diagnostic.replace operator.span "-(-"; Diagnostic.insert operand_span.stop ")" ]

(* [A => 1,]: arms are separated by line breaks. *)
let match_arm_comma cursor ~(comma : Token.t) =
  report cursor Match_arm_comma comma.span "`match` arms are separated by line breaks, not commas"
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
    "Truss has no conditional operator; write `if x { a } else { b }`" "Write an `if` expression"
    [
      Diagnostic.replace whole
        (Printf.sprintf "if %s { %s } else { %s }" (node_text cursor condition.span)
           (node_text cursor then_.span) (node_text cursor else_.span));
    ]

(* [let mut x]. *)
let let_mut cursor ~(let_token : Token.t) ~(mut_token : Token.t) =
  report cursor Let_mut mut_token.span
    "a variable that can change is declared with `var`, not `let mut`" "Write `var`"
    [ Diagnostic.replace (Source.span let_token.span.start mut_token.span.stop) "var" ]

(* [&x] and [&mut x]: arguments are marked with [mut] or [own], never [&]. *)
let address_of cursor ~(ampersand : Token.t) ~(next : Token.t) =
  let marked = match next.kind with Keyword Mut -> "`mut x`" | _ -> "`x`" in
  (* Between two names, as in [match& x], a space keeps them apart. *)
  let source = Source.text cursor.Cursor.source in
  let is_name_byte character =
    match character with 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true | _ -> false
  in
  let separator =
    if ampersand.span.start > 0 && is_name_byte source.[ampersand.span.start - 1] then " " else ""
  in
  report cursor Address_of ampersand.span
    (Printf.sprintf
       "Truss has no `&`; write %s, marking a place with `mut` or `own` only when it is changed or \
        given up"
       marked)
    "Remove the `&`"
    [ Diagnostic.replace (through_next ampersand next) separator ]

(* [|x| x + 1] and [|| x]. *)
let closure_bars cursor ~(opening : Token.t) ~(closing : Token.t) ~(body : expression) =
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
    | _ -> edits @ [ Diagnostic.insert body_span.start "{ "; Diagnostic.insert body_span.stop " }" ]
  in
  report cursor Closure_bars opening.span "a lambda is written `fn(x) { x + 1 }`"
    "Write `fn(...) { ... }`" edits

(* [Point { x: 1.0 }]: records are built with parentheses. *)
let brace_record cursor ~(name_stop : int) ~(opening : Token.t) ~(first : Token.t)
    ~(last_stop : int) ~(closing : Token.t) =
  report cursor Brace_record opening.span
    "records are built with parentheses: `Point(x: 1.0, y: 2.0)`" "Use parentheses"
    [
      Diagnostic.replace (Source.span name_stop first.span.start) "(";
      Diagnostic.replace (Source.span last_stop closing.span.stop) ")";
    ]

(* [parse::<Int64>(text)]. *)
let turbofish cursor ~(colons : Token.t) ~(less : Token.t) ~(greater : Token.t) =
  report cursor Turbofish less.span "type arguments go in square brackets: `parse[Int64](text)`"
    "Use square brackets"
    [
      Diagnostic.replace (Source.span colons.span.start less.span.stop) "[";
      Diagnostic.replace greater.span "]";
    ]

(* The name a lambda's parameter gets in place of [it]: the singular of the
   collection's name, as in [items.map(fn(item) { item.name })], or
   [element]. *)
let parameter_name (callee : expression) =
  let receiver = match callee.kind with Member (receiver, _) -> Some receiver | _ -> None in
  match receiver with
  | Some { kind = Name { modules = []; last }; _ }
    when String.length last.text > 1 && String.ends_with ~suffix:"s" last.text ->
      String.sub last.text 0 (String.length last.text - 1)
  | _ -> "element"

(* [items.map { it.name }]: a lambda goes inside the parentheses. *)
let trailing_lambda cursor ~(callee : expression) ~(opening : Token.t) ~(closing : Token.t)
    ~(uses : Token.t list) =
  let parameter = parameter_name callee in
  let callee_stop = (Cursor.absolute cursor callee.span).stop in
  report cursor Trailing_lambda opening.span
    (Printf.sprintf
       "a lambda is passed inside the parentheses, with a named parameter: `fn(%s) { ... }`"
       parameter)
    "Pass a lambda"
    (Diagnostic.replace
       (Source.span callee_stop opening.span.start)
       (Printf.sprintf "(fn(%s) " parameter)
    :: Diagnostic.insert closing.span.stop ")"
    :: List.map (fun (token : Token.t) -> Diagnostic.replace token.span parameter) uses)

(* [x as Int64]. *)
let as_conversion cursor ~(value : expression) ~(as_token : Token.t) ~(target : type_expression) =
  let whole =
    Source.span (Cursor.absolute cursor value.span).start (Cursor.absolute cursor target.span).stop
  in
  let target_text = node_text cursor target.span in
  report cursor As_conversion as_token.span
    (Printf.sprintf
       "Truss has no `as`; write `%s.from(x)`, or `%s.try_from(x)` when the conversion can lose \
        information"
       target_text target_text)
    (Printf.sprintf "Write `%s.from(...)`" target_text)
    [
      Diagnostic.replace whole
        (Printf.sprintf "%s.from(%s)" target_text (node_text cursor value.span));
    ]

(* [elif]: written after the [}] that ends an [if]. *)
let elif cursor ~(previous_stop : int) ~(elif_token : Token.t) =
  report cursor Elif elif_token.span "Truss writes `else if`, not `elif`" "Write `else if`"
    [ Diagnostic.replace (Source.span previous_stop elif_token.span.stop) " else if" ]

(* [loop {]. *)
let loop cursor ~(loop_token : Token.t) =
  report cursor Reserved_word loop_token.span "Truss has no `loop`; write `while true`"
    "Write `while true`"
    [ Diagnostic.replace loop_token.span "while true" ]

(* [const] and [static] before a constant. *)
let constant_keyword cursor ~(token : Token.t) =
  let word = Cursor.text cursor token.span in
  report cursor Reserved_word token.span
    (Printf.sprintf "Truss has no `%s`; a constant is a `let` at the top level" word)
    "Write `let`"
    [ Diagnostic.replace token.span "let" ]

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
    [ Diagnostic.replace operator.span "-(-"; Diagnostic.insert operand_span.stop ")" ]

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
  (* Between two words, as in [match& x], a space keeps them apart. *)
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
        given up."
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
    | _ -> edits @ [ Diagnostic.insert body_span.start "{ "; Diagnostic.insert body_span.stop " }" ]
  in
  (* Before the [else] of a [let ... else], an expression cannot end with
     the lambda's [}]. *)
  let edits =
    if before_else then
      (Diagnostic.insert opening.span.start "(" :: edits) @ [ Diagnostic.insert body_span.stop ")" ]
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

(* The singular of a plural English noun, for the plurals that are plain
   to undo: [items] and [entries], but not [statuses] or [classes]. *)
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
   collection's name, as in [items.map(fn(item) { item.name })], when that
   is plain to work out, and otherwise [element]. *)
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
    :: Diagnostic.insert closing.span.stop ")"
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

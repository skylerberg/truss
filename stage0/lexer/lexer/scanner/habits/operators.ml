type scanned = Lexed of Token.kind | Ellipsis

let replace cursor ~start ~length ~replacements ~code message =
  Cursor.report cursor ~code
    ~fixes:(Cursor.list_code_fixes cursor (Source.make_span start (start + length)) replacements)
    (Source.make_span start (start + length))
    message

let scan (cursor : Cursor.t) =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let make_lexed kind length =
    cursor.position <- start + length;
    Some (Lexed kind)
  in
  let make_replaced ~length ~replacements ~message kind =
    replace cursor ~start ~length ~replacements ~code:Foreign_operator message;
    make_lexed kind length
  in
  if is 0 ':' && is 1 '=' then make_lexed (Foreign Colon_equal) 2
  else if is 0 ':' && is 1 ':' && is 2 '<' then make_lexed (Foreign Colon_colon) 2
  else if is 0 ':' && is 1 ':' then begin
    replace cursor ~start ~length:2 ~replacements:[ "." ] ~code:Path_separator
      "Truss separates the names of a path with `.`, as in `json.parse` and `Shape.Circle`.";
    make_lexed (Punctuation Dot) 2
  end
  else if is 0 '-' && is 1 '-' then make_lexed (Foreign Minus_minus) 2
  else if is 0 '+' && is 1 '+' then make_lexed (Foreign Plus_plus) 2
  else if is 0 '*' && is 1 '*' then make_lexed (Foreign Star_star) 2
  else if is 0 '|' && is 1 '>' then make_lexed (Foreign Pipe_greater) 2
  else if is 0 '.' && is 1 '.' && is 2 '<' then
    make_replaced ~length:3 ~replacements:[ ".." ] ~message:"Truss has no `..<`; write `..`."
      (Punctuation Dot_dot)
  else if is 0 '<' && is 1 '>' then
    make_replaced ~length:2 ~replacements:[ "!=" ] ~message:"Truss has no `<>`; write `!=`."
      (Punctuation Not_equal)
  else if (is 0 '=' || is 0 '!') && is 1 '=' && is 2 '=' && not (is 3 '=') then (
    let written, replacement, kind =
      if is 0 '=' then ("===", "==", Token.Equal_equal) else ("!==", "!=", Not_equal)
    in
    replace cursor ~start ~length:3 ~replacements:[ replacement ] ~code:Strict_equality
      (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
         replacement);
    make_lexed (Punctuation kind) 3)
  else if is 0 '.' && is 1 '.' && is 2 '.' then begin
    cursor.position <- start + 3;
    cursor.line_is_blank <- false;
    Some Ellipsis
  end
  else None

let lex_ellipsis cursor ~start ~follows_operand ~operand_follows =
  let make_replaced ~replacements message kind =
    replace cursor ~start ~length:3 ~replacements ~code:Foreign_operator message;
    Some kind
  in
  match (follows_operand, operand_follows) with
  | true, true ->
      make_replaced ~replacements:[ ".."; "..=" ]
        "Truss has no `...`. A range that leaves out its end is written `..`, and one that \
         includes its end is written `..=`."
        (Token.Punctuation Dot_dot_equal)
  | false, false ->
      make_replaced ~replacements:[ "todo" ]
        "Truss has no `...`; code that is not written yet is `todo`." (Token.Keyword Todo)
  | _ ->
      Cursor.report cursor ~code:Foreign_operator
        (Source.make_span start (start + 3))
        "Truss has no `...`: it has no spread or rest operator, and a function takes a list where \
         it takes any number of values.";
      None

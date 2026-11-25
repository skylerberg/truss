type scanned = Lexed of Token.kind | Ellipsis

let replace cursor ~start ~length ~replacements problem =
  Cursor.report cursor
    ~fixes:(Cursor.list_code_fixes cursor (Source.make_span start (start + length)) replacements)
    (Source.make_span start (start + length))
    problem

let scan (cursor : Cursor.t) =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let make_lexed kind length =
    cursor.position <- start + length;
    Some (Lexed kind)
  in
  let make_replaced ~length ~replacements ~operator kind =
    replace cursor ~start ~length ~replacements (Foreign_operator operator);
    make_lexed kind length
  in
  if is 0 ':' && is 1 '=' then make_lexed (Foreign Colon_equal) 2
  else if is 0 ':' && is 1 ':' && is 2 '<' then make_lexed (Foreign Colon_colon) 2
  else if is 0 ':' && is 1 ':' then begin
    replace cursor ~start ~length:2 ~replacements:[ "." ] Path_separator;
    make_lexed (Punctuation Dot) 2
  end
  else if is 0 '-' && is 1 '-' then make_lexed (Foreign Minus_minus) 2
  else if is 0 '+' && is 1 '+' then make_lexed (Foreign Plus_plus) 2
  else if is 0 '*' && is 1 '*' then make_lexed (Foreign Star_star) 2
  else if is 0 '|' && is 1 '>' then make_lexed (Foreign Pipe_greater) 2
  else if is 0 '.' && is 1 '.' && is 2 '<' then
    make_replaced ~length:3 ~replacements:[ ".." ] ~operator:Half_open_range (Punctuation Dot_dot)
  else if is 0 '<' && is 1 '>' then
    make_replaced ~length:2 ~replacements:[ "!=" ] ~operator:Diamond (Punctuation Not_equal)
  else if (is 0 '=' || is 0 '!') && is 1 '=' && is 2 '=' && not (is 3 '=') then (
    let written, replacement, kind =
      if is 0 '=' then ("===", "==", Token.Equal_equal) else ("!==", "!=", Not_equal)
    in
    replace cursor ~start ~length:3 ~replacements:[ replacement ]
      (Strict_equality { written; replacement });
    make_lexed (Punctuation kind) 3)
  else if is 0 '.' && is 1 '.' && is 2 '.' then begin
    cursor.position <- start + 3;
    cursor.line_is_blank <- false;
    Some Ellipsis
  end
  else None

let lex_ellipsis cursor ~start ~follows_operand ~operand_follows =
  let make_replaced ~replacements operator kind =
    replace cursor ~start ~length:3 ~replacements (Foreign_operator operator);
    Some kind
  in
  match (follows_operand, operand_follows) with
  | true, true ->
      make_replaced ~replacements:[ ".."; "..=" ] Range_ellipsis (Token.Punctuation Dot_dot_equal)
  | false, false -> make_replaced ~replacements:[ "todo" ] Todo_ellipsis (Token.Keyword Todo)
  | _ ->
      Cursor.report cursor (Source.make_span start (start + 3)) (Foreign_operator Spread_ellipsis);
      None

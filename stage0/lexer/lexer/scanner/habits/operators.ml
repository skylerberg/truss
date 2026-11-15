open Token
open Cursor

type scanned = Lexed of Token.kind | Ellipsis

let replace cursor ~start ~length ~replacements ~code message =
  report cursor ~code
    ~fixes:
      (List.map
         (fun replacement ->
           Diagnostic.fix
             ("Write `" ^ replacement ^ "`")
             [ Diagnostic.replace (span start (start + length)) replacement ])
         replacements)
    (span start (start + length))
    message

let scan cursor =
  let start = cursor.position in
  let is offset character = is_at cursor (start + offset) character in
  let lexed kind length =
    cursor.position <- start + length;
    Some (Lexed kind)
  in
  let replaced ~length ~replacements ~message kind =
    replace cursor ~start ~length ~replacements ~code:Foreign_operator message;
    lexed kind length
  in
  if is 0 ':' && is 1 '=' then lexed (Foreign Colon_equal) 2
  else if is 0 '-' && is 1 '-' then lexed (Foreign Minus_minus) 2
  else if is 0 '+' && is 1 '+' then lexed (Foreign Plus_plus) 2
  else if is 0 '*' && is 1 '*' then lexed (Foreign Star_star) 2
  else if is 0 '|' && is 1 '>' then lexed (Foreign Pipe_greater) 2
  else if is 0 '.' && is 1 '.' && is 2 '<' then
    replaced ~length:3 ~replacements:[ ".." ] ~message:"Truss has no `..<`; write `..`."
      (Punctuation Dot_dot)
  else if is 0 '<' && is 1 '>' then
    replaced ~length:2 ~replacements:[ "!=" ] ~message:"Truss has no `<>`; write `!=`."
      (Punctuation Not_equal)
  else if (is 0 '=' || is 0 '!') && is 1 '=' && is 2 '=' && not (is 3 '=') then (
    let written, replacement, kind =
      if is 0 '=' then ("===", "==", Equal_equal) else ("!==", "!=", Not_equal)
    in
    replace cursor ~start ~length:3 ~replacements:[ replacement ] ~code:Strict_equality
      (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
         replacement);
    lexed (Punctuation kind) 3)
  else if is 0 '.' && is 1 '.' && is 2 '.' then begin
    cursor.position <- start + 3;
    cursor.line_is_blank <- false;
    Some Ellipsis
  end
  else None

let ellipsis cursor ~start ~follows_operand ~operand_follows =
  let replaced ~replacements message kind =
    replace cursor ~start ~length:3 ~replacements ~code:Foreign_operator message;
    Some kind
  in
  match (follows_operand, operand_follows) with
  | true, true ->
      replaced ~replacements:[ ".."; "..=" ]
        "Truss has no `...`. A range that leaves out its end is written `..`, and one that \
         includes its end is written `..=`."
        (Punctuation Dot_dot_equal)
  | false, false ->
      replaced ~replacements:[ "todo" ]
        "Truss has no `...`; code that is not written yet is `todo`." (Keyword Todo)
  | _ ->
      report cursor ~code:Foreign_operator
        (span start (start + 3))
        "Truss has no `...`: it has no spread or rest operator, and a function takes a list where \
         it takes any number of values.";
      None

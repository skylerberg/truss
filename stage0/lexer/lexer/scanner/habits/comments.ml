(* The comments, attributes, and `;` of other languages, which lex as
   whitespace. A comment or an attribute has no fix: removing it would delete
   what its author wrote. *)

open Cursor

let comment_message = "Truss has no comments. Say this with a name, a contract, or a test instead."

let line_comment cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Comment (span start stop) comment_message

let block_comment cursor =
  let start = cursor.position in
  let first_line_break = ref None in
  let rec loop depth position =
    let current = byte cursor position in
    if current < 0 then (position, false)
    else if current = Char.code '*' && byte cursor (position + 1) = Char.code '/' then
      if depth = 1 then (position + 2, true) else loop (depth - 1) (position + 2)
    else if current = Char.code '/' && byte cursor (position + 1) = Char.code '*' then
      loop (depth + 1) (position + 2)
    else begin
      if is_line_break current && !first_line_break = None then
        first_line_break := Some (span position (position + line_break_length cursor position));
      loop depth (position + 1)
    end
  in
  let stop, closed = loop 1 (start + 2) in
  cursor.position <- stop;
  if not closed then cursor.unterminated_at_end <- true;
  cursor.line_is_blank <- false;
  (* A comment that spans lines separates the tokens around it like a line
     break. *)
  (match !first_line_break with
  | Some line_break when cursor.first_line_break = None ->
      cursor.first_line_break <- Some line_break
  | _ -> ());
  report cursor ~code:Comment (span start stop)
    (if closed then comment_message
     else comment_message ^ " This comment is never closed, so it runs to the end of the file.")

let semicolon cursor =
  let start = cursor.position in
  cursor.position <- start + 1;
  cursor.line_is_blank <- false;
  let rec next_code position =
    let position = skip_spaces cursor position in
    if byte cursor position = Char.code ';' then next_code (position + 1) else position
  in
  let next = next_code (start + 1) in
  (* Mid-line, the next token starts a new statement, unless it is a `}`. *)
  let line_break = not (is_end_of_line (byte cursor next) || byte cursor next = Char.code '}') in
  if line_break && cursor.first_line_break = None then
    cursor.first_line_break <- Some (span start (start + 1));
  report cursor ~code:Semicolon
    ~fixes:
      [
        Diagnostic.fix
          (if line_break then "Replace the `;` with a line break" else "Remove the `;`")
          [ Source_text.remove_trivia cursor ~start ~stop:(start + 1) ~line_break ];
      ]
    (span start (start + 1))
    "Statements end at a line break. Truss has no `;`."

(* An attribute of Rust, `#[derive(...)]` or `#![...]`: like a comment, it
   lexes as nothing, up to the end of its line. *)
let attribute cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Attribute (span start stop)
    "Truss has no attributes. A type lists the traits it derives in a `derives` clause, and a test \
     is a `test` definition."

(* A comment, an attribute, or a `;` at the cursor, skipped and reported.
   Inside an interpolation, where it cannot end its line, it is rejected.
   [false] when none starts there. *)
let scan cursor ~inline =
  let start = cursor.position in
  let current = byte cursor start and next = byte cursor (start + 1) in
  let is character = current = Char.code character in
  let rejected ?code length message =
    Source_text.reject ?code cursor ~length message;
    true
  in
  if is '/' && (next = Char.code '/' || next = Char.code '*') then
    if inline then rejected ~code:Comment 2 comment_message
    else begin
      if next = Char.code '/' then line_comment cursor else block_comment cursor;
      true
    end
  else if
    is '#'
    && (next = Char.code '[' || (next = Char.code '!' && byte cursor (start + 2) = Char.code '['))
  then
    if inline then rejected ~code:Attribute 1 "Truss has no attributes."
    else begin
      attribute cursor;
      true
    end
  else if is '#' then
    if inline then rejected ~code:Comment 1 comment_message
    else begin
      line_comment cursor;
      true
    end
  else if is ';' then
    if inline then rejected ~code:Semicolon 1 "Truss has no `;`."
    else begin
      semicolon cursor;
      true
    end
  else false

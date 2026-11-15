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
    if at_end cursor position then (position, false)
    else if is_at cursor position '*' && is_at cursor (position + 1) '/' then
      if depth = 1 then (position + 2, true) else loop (depth - 1) (position + 2)
    else if is_at cursor position '/' && is_at cursor (position + 1) '*' then
      loop (depth + 1) (position + 2)
    else begin
      if is_line_break (char cursor position) && !first_line_break = None then
        first_line_break := Some (span position (position + line_break_length cursor position));
      loop depth (position + 1)
    end
  in
  let stop, closed = loop 1 (start + 2) in
  cursor.position <- stop;
  if not closed then cursor.unterminated_at_end <- true;
  cursor.line_is_blank <- false;
  (match !first_line_break with
  | Some line_break when cursor.first_line_break = None ->
      cursor.first_line_break <- Some line_break
  | _ -> ());
  report cursor ~code:Comment (span start stop)
    (if closed then comment_message
     else comment_message ^ " This comment is never closed, so it runs to the end of the file.")

let semicolon cursor =
  cursor.semicolons <- cursor.position :: cursor.semicolons;
  cursor.position <- cursor.position + 1;
  cursor.line_is_blank <- false

let end_semicolons cursor ~line_break =
  match List.rev cursor.semicolons with
  | [] -> ()
  | first :: _ as semicolons ->
      cursor.semicolons <- [];
      if line_break && cursor.first_line_break = None then
        cursor.first_line_break <- Some (span first (first + 1));
      List.iter
        (fun start ->
          report cursor ~code:Semicolon
            ~fixes:
              [
                Diagnostic.fix
                  (if line_break then "Replace the `;` with a line break" else "Remove the `;`")
                  [ Source_text.remove_trivia cursor ~start ~stop:(start + 1) ~line_break ];
              ]
            (span start (start + 1))
            "Statements end at a line break. Truss has no `;`.")
        semicolons

let attribute cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Attribute (span start stop)
    "Truss has no attributes. A type lists the traits it derives in a `derives` clause, and a test \
     is a `test` definition."

let scan cursor ~inline =
  let start = cursor.position in
  let is offset character = is_at cursor (start + offset) character in
  let rejected ?code length message =
    Source_text.reject ?code cursor ~length message;
    true
  in
  if is 0 '/' && (is 1 '/' || is 1 '*') then
    if inline then rejected ~code:Comment 2 comment_message
    else begin
      if is 1 '/' then line_comment cursor else block_comment cursor;
      true
    end
  else if is 0 '#' && (is 1 '[' || (is 1 '!' && is 2 '[')) then
    if inline then rejected ~code:Attribute 1 "Truss has no attributes."
    else begin
      attribute cursor;
      true
    end
  else if is 0 '#' then
    if inline then rejected ~code:Comment 1 comment_message
    else begin
      line_comment cursor;
      true
    end
  else if is 0 ';' then
    if inline then rejected ~code:Semicolon 1 "Truss has no `;`."
    else begin
      semicolon cursor;
      true
    end
  else false

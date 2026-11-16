let comment_message = "Truss has no comments. Say this with a name, a contract, or a test instead."

let lex_line_comment (cursor : Cursor.t) =
  let start = cursor.position in
  let stop = Cursor.compute_end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  Cursor.report cursor ~code:Comment (Source.span start stop) comment_message

let lex_block_comment (cursor : Cursor.t) =
  let start = cursor.position in
  let first_line_break = ref None in
  let rec loop depth position =
    if Cursor.is_at_end cursor position then (position, false)
    else if Cursor.is_at cursor position '*' && Cursor.is_at cursor (position + 1) '/' then
      if depth = 1 then (position + 2, true) else loop (depth - 1) (position + 2)
    else if Cursor.is_at cursor position '/' && Cursor.is_at cursor (position + 1) '*' then
      loop (depth + 1) (position + 2)
    else begin
      if Cursor.is_line_break (Cursor.lookup_char cursor position) && !first_line_break = None then
        first_line_break :=
          Some (Source.span position (position + Cursor.measure_line_break cursor position));
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
  Cursor.report cursor ~code:Comment (Source.span start stop)
    (if closed then comment_message
     else comment_message ^ " This comment is never closed, so it runs to the end of the file.")

let record_semicolon (cursor : Cursor.t) =
  cursor.semicolons <- cursor.position :: cursor.semicolons;
  cursor.position <- cursor.position + 1;
  cursor.line_is_blank <- false

let report_semicolons (cursor : Cursor.t) ~line_break =
  match List.rev cursor.semicolons with
  | [] -> ()
  | first :: _ as semicolons ->
      cursor.semicolons <- [];
      if line_break && cursor.first_line_break = None then
        cursor.first_line_break <- Some (Source.span first (first + 1));
      List.iter
        (fun start ->
          Cursor.report cursor ~code:Semicolon
            ~fixes:
              [
                Diagnostic.fix
                  (if line_break then "Replace the `;` with a line break" else "Remove the `;`")
                  [ Source_text.remove_trivia cursor ~start ~stop:(start + 1) ~line_break ];
              ]
            (Source.span start (start + 1))
            "Statements end at a line break. Truss has no `;`.")
        semicolons

let lex_attribute (cursor : Cursor.t) =
  let start = cursor.position in
  let stop = Cursor.compute_end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  Cursor.report cursor ~code:Attribute (Source.span start stop)
    "Truss has no attributes. A type lists the traits it derives in a `derives` clause, and a test \
     is a `test` definition."

let scan (cursor : Cursor.t) ~inline =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let rejected ~code length message =
    Source_text.reject ~code cursor ~length message;
    true
  in
  if is 0 '/' && (is 1 '/' || is 1 '*') then
    if inline then rejected ~code:Comment 2 comment_message
    else begin
      if is 1 '/' then lex_line_comment cursor else lex_block_comment cursor;
      true
    end
  else if is 0 '#' && (is 1 '[' || (is 1 '!' && is 2 '[')) then
    if inline then rejected ~code:Attribute 1 "Truss has no attributes."
    else begin
      lex_attribute cursor;
      true
    end
  else if is 0 '#' then
    if inline then rejected ~code:Comment 1 comment_message
    else begin
      lex_line_comment cursor;
      true
    end
  else if is 0 ';' then
    if inline then rejected ~code:Semicolon 1 "Truss has no `;`."
    else begin
      record_semicolon cursor;
      true
    end
  else false

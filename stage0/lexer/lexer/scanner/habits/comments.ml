let make_deletion cursor ~start ~stop ~line_break : Syntax_catalog.Lexing.fix =
  { action = Delete_comment; edits = [ Source_text.remove_trivia cursor ~start ~stop ~line_break ] }

let lex_line_comment (cursor : Cursor.t) =
  let start = cursor.position in
  let stop = Cursor.compute_end_of_line cursor start in
  let deletion = make_deletion cursor ~start ~stop ~line_break:false in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  Cursor.report cursor ~fixes:[ deletion ] (Source.make_span start stop)
    (Comment { is_closed = true })

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
          Some (Source.make_span position (position + Cursor.measure_line_break cursor position));
      loop depth (position + 1)
    end
  in
  let stop, closed = loop 1 (start + 2) in
  let fixes =
    if closed then
      [ make_deletion cursor ~start ~stop ~line_break:(Option.is_some !first_line_break) ]
    else []
  in
  cursor.position <- stop;
  if not closed then cursor.unterminated_at_end <- true;
  cursor.line_is_blank <- false;
  (match !first_line_break with
  | Some line_break when cursor.first_line_break = None ->
      cursor.first_line_break <- Some line_break
  | _ -> ());
  Cursor.report cursor ~fixes (Source.make_span start stop) (Comment { is_closed = closed })

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
        cursor.first_line_break <- Some (Source.make_span first (first + 1));
      List.iter
        (fun start ->
          Cursor.report cursor
            ~fixes:
              [
                {
                  action = (if line_break then Replace_semicolon else Remove_semicolon);
                  edits = [ Source_text.remove_trivia cursor ~start ~stop:(start + 1) ~line_break ];
                };
              ]
            (Source.make_span start (start + 1))
            Semicolon)
        semicolons

let lex_attribute (cursor : Cursor.t) =
  let start = cursor.position in
  let stop = Cursor.compute_end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  Cursor.report cursor (Source.make_span start stop) Attribute

let scan (cursor : Cursor.t) ~inline =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let reject length problem =
    Source_text.reject cursor ~length problem;
    true
  in
  if is 0 '/' && (is 1 '/' || is 1 '*') then
    if inline then reject 2 (Comment { is_closed = true })
    else begin
      if is 1 '/' then lex_line_comment cursor else lex_block_comment cursor;
      true
    end
  else if is 0 '#' && (is 1 '[' || (is 1 '!' && is 2 '[')) then
    if inline then reject 1 Inline_attribute
    else begin
      lex_attribute cursor;
      true
    end
  else if is 0 '#' then
    if inline then reject 1 (Comment { is_closed = true })
    else begin
      lex_line_comment cursor;
      true
    end
  else if is 0 ';' then
    if inline then reject 1 Inline_semicolon
    else begin
      record_semicolon cursor;
      true
    end
  else false

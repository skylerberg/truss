type context = Code | Ordinary_string | Raw_string

let remove_trivia cursor ~start ~stop ~line_break : Syntax_catalog.Lexing.edit =
  let before = Cursor.count_spaces_before cursor start in
  let after = Cursor.skip_spaces cursor stop in
  let code_before = not (Cursor.has_only_spaces_before cursor start) in
  let code_after = not (Cursor.is_end_of_line cursor after) in
  match (code_before, code_after) with
  | true, true ->
      {
        replaced = Source.make_span before after;
        code =
          (if line_break then Line_break_indented (Cursor.extract_indentation cursor start)
           else Space);
      }
  | true, false -> { replaced = Source.make_span before after; code = Removed }
  | false, true -> { replaced = Source.make_span start after; code = Removed }
  | false, false ->
      let line_start = Source.compute_line_start cursor.source start in
      let stop =
        if Cursor.is_at_end cursor after then after
        else after + Cursor.measure_line_break cursor after
      in
      { replaced = Source.make_span line_start stop; code = Removed }

let report_forbidden_run (cursor : Cursor.t) ~context =
  let start = cursor.position in
  let rec collect characters =
    if Cursor.is_at_end cursor cursor.position then List.rev characters
    else
      let decoded = Cursor.decode cursor cursor.position in
      let scalar_value = Uchar.utf_decode_uchar decoded in
      if Uchar.utf_decode_is_valid decoded && Unicode.is_forbidden scalar_value then begin
        cursor.position <- cursor.position + Uchar.utf_decode_length decoded;
        collect (scalar_value :: characters)
      end
      else List.rev characters
  in
  let characters = collect [] in
  let stop = cursor.position in
  let is_plural = List.length characters > 1 in
  let fixes : Syntax_catalog.Lexing.fix list =
    match context with
    | Code ->
        [
          {
            action = Delete_characters { is_plural };
            edits = [ remove_trivia cursor ~start ~stop ~line_break:false ];
          };
        ]
    | Ordinary_string ->
        let code_points = List.map Uchar.to_int characters in
        [
          {
            action = Replace_with_escapes code_points;
            edits = [ { replaced = Source.make_span start stop; code = Escapes code_points } ];
          };
        ]
    | Raw_string -> []
  in
  Cursor.report cursor ~fixes (Source.make_span start stop)
    (Forbidden_characters
       {
         characters =
           List.map
             (fun value : Syntax_catalog.Lexing.forbidden ->
               {
                 code_point = Uchar.to_int value;
                 name = Unicode.find_forbidden_name value;
                 kind =
                   (if Unicode.is_bidi_control value then Bidirectional_control
                    else if Unicode.is_control value then Control_character
                    else Invisible_character);
               })
             characters;
         context =
           (match context with
           | Code -> In_code
           | Ordinary_string -> In_ordinary_string
           | Raw_string -> In_raw_string);
       })

let report_invalid_run (cursor : Cursor.t) =
  let start = cursor.position in
  while
    (not (Cursor.is_at_end cursor cursor.position))
    && not (Uchar.utf_decode_is_valid (Cursor.decode cursor cursor.position))
  do
    cursor.position <- cursor.position + 1
  done;
  Cursor.report cursor (Source.make_span start cursor.position) Invalid_utf8

let copy_plain (cursor : Cursor.t) buffer ~is_special =
  let start = cursor.position in
  let rec stop index =
    if Cursor.is_at_end cursor index then index
    else
      let current = Cursor.lookup_char cursor index in
      if (current >= ' ' && current < '\x7F' && not (is_special current)) || current = '\t' then
        stop (index + 1)
      else index
  in
  let stop = stop start in
  if stop > start then begin
    Buffer.add_substring buffer cursor.text start (stop - start);
    cursor.position <- stop
  end

let read_character cursor buffer ~context =
  let decoded = Cursor.decode cursor cursor.position in
  if not (Uchar.utf_decode_is_valid decoded) then report_invalid_run cursor
  else if Unicode.is_forbidden (Uchar.utf_decode_uchar decoded) then
    report_forbidden_run cursor ~context
  else begin
    let length = Uchar.utf_decode_length decoded in
    Buffer.add_substring buffer cursor.text cursor.position length;
    cursor.position <- cursor.position + length
  end

let consume_line_break (cursor : Cursor.t) =
  let start = cursor.position in
  let length = Cursor.measure_line_break cursor start in
  if length = 1 && Cursor.is_at cursor start '\r' then
    Cursor.report cursor
      ~fixes:
        [
          {
            action = Replace_with_line_feed;
            edits = [ { replaced = Source.make_span start (start + 1); code = Line_feed } ];
          };
        ]
      (Source.make_span start (start + 1))
      Carriage_return;
  cursor.position <- start + length;
  Source.make_span start cursor.position

let note_line_break (cursor : Cursor.t) line_break =
  if cursor.first_line_break <> None && cursor.line_is_blank then cursor.blank_line <- true;
  if cursor.first_line_break = None then cursor.first_line_break <- Some line_break;
  cursor.line_is_blank <- true

let reject (cursor : Cursor.t) ~length problem =
  let start = cursor.position in
  cursor.position <- start + length;
  cursor.line_is_blank <- false;
  Cursor.report cursor (Source.make_span start (start + length)) problem

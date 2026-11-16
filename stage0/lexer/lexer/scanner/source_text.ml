type context = Code | Ordinary_string | Raw_string

let remove_trivia cursor ~start ~stop ~line_break =
  let before = Cursor.spaces_before cursor start in
  let after = Cursor.skip_spaces cursor stop in
  let code_before = not (Cursor.only_spaces_before cursor start) in
  let code_after = not (Cursor.is_end_of_line cursor after) in
  match (code_before, code_after) with
  | true, true ->
      Diagnostic.replace (Cursor.span before after)
        (if line_break then "\n" ^ Cursor.indentation cursor start else " ")
  | true, false -> Diagnostic.delete (Cursor.span before after)
  | false, true -> Diagnostic.delete (Cursor.span start after)
  | false, false ->
      let line_start = Source.line_start cursor.source start in
      let stop =
        if Cursor.at_end cursor after then after else after + Cursor.line_break_length cursor after
      in
      Diagnostic.delete (Cursor.span line_start stop)

let forbidden_run (cursor : Cursor.t) ~context =
  let start = cursor.position in
  let rec collect characters =
    let decoded = Cursor.decode cursor cursor.position in
    if Unicode.Decoded.is_valid decoded && Unicode.is_forbidden (Unicode.Decoded.code_point decoded)
    then begin
      cursor.position <- cursor.position + Unicode.Decoded.length decoded;
      collect (Unicode.Decoded.code_point decoded :: characters)
    end
    else List.rev characters
  in
  let characters = collect [] in
  let stop = cursor.position in
  let names = String.concat ", " (List.map Cursor.describe_code_point characters) in
  let reasons =
    List.sort_uniq compare
      (List.map
         (fun value ->
           if Unicode.is_bidi_control value then
             "Bidirectional controls can make code display differently from how it compiles."
           else if Unicode.is_control value then
             "Control characters can make a terminal hide or rewrite text."
           else "Invisible characters can hide text from a reader.")
         characters)
  in
  let plural = List.length characters > 1 in
  let base =
    Printf.sprintf "%s %s not allowed in source files. %s" names
      (if plural then "are" else "is")
      (String.concat " " reasons)
  in
  let message, fixes =
    match context with
    | Code ->
        ( base,
          [
            Diagnostic.fix
              (if plural then "Delete the characters" else "Delete the character")
              [ remove_trivia cursor ~start ~stop ~line_break:false ];
          ] )
    | Ordinary_string ->
        let escapes = String.concat "" (List.map (Printf.sprintf "\\u{%X}") characters) in
        ( base ^ " Write it as an escape, so that it can be seen.",
          [
            Diagnostic.fix
              ("Replace with `" ^ escapes ^ "`")
              [ Diagnostic.replace (Cursor.span start stop) escapes ];
          ] )
    | Raw_string ->
        ( base
          ^ " A raw string has no escapes, so write the text as an ordinary string, with the \
             character as an escape such as `\\u{200B}`.",
          [] )
  in
  Cursor.report cursor ~fixes ~code:Forbidden_character (Cursor.span start stop) message

let invalid_run (cursor : Cursor.t) =
  let start = cursor.position in
  while
    (not (Cursor.at_end cursor cursor.position))
    && not (Unicode.Decoded.is_valid (Cursor.decode cursor cursor.position))
  do
    cursor.position <- cursor.position + 1
  done;
  Cursor.report cursor ~code:Invalid_utf8
    (Cursor.span start cursor.position)
    "Source files must be UTF-8, and these bytes are not valid UTF-8."

let copy_plain (cursor : Cursor.t) buffer ~special =
  let start = cursor.position in
  let rec stop index =
    if Cursor.at_end cursor index then index
    else
      let current = Cursor.char cursor index in
      if (current >= ' ' && current < '\x7F' && not (special current)) || current = '\t' then
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
  if not (Unicode.Decoded.is_valid decoded) then invalid_run cursor
  else if Unicode.is_forbidden (Unicode.Decoded.code_point decoded) then
    forbidden_run cursor ~context
  else begin
    Buffer.add_substring buffer cursor.text cursor.position (Unicode.Decoded.length decoded);
    cursor.position <- cursor.position + Unicode.Decoded.length decoded
  end

let consume_line_break (cursor : Cursor.t) =
  let start = cursor.position in
  let length = Cursor.line_break_length cursor start in
  if length = 1 && Cursor.is_at cursor start '\r' then
    Cursor.report cursor ~code:Carriage_return
      ~fixes:
        [
          Diagnostic.fix "Replace with a line feed"
            [ Diagnostic.replace (Cursor.span start (start + 1)) "\n" ];
        ]
      (Cursor.span start (start + 1))
      "A carriage return is a line break only before a line feed.";
  cursor.position <- start + length;
  Cursor.span start cursor.position

let note_line_break (cursor : Cursor.t) line_break =
  if cursor.first_line_break <> None && cursor.line_is_blank then cursor.blank_line <- true;
  if cursor.first_line_break = None then cursor.first_line_break <- Some line_break;
  cursor.line_is_blank <- true

let reject ?(code = Diagnostic.Code.Unexpected_character) (cursor : Cursor.t) ~length message =
  let start = cursor.position in
  cursor.position <- start + length;
  cursor.line_is_blank <- false;
  Cursor.report cursor ~code (Cursor.span start (start + length)) message

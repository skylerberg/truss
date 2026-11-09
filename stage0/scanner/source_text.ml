(* Checks on the source text (LEXER.md, "Source text"): UTF-8, forbidden
   characters, and line breaks, in code and in strings alike. *)

open Cursor

type context = Code | Ordinary_string | Raw_string

(* The edit that removes trivia: [start, stop) holds text that the scanner
   treats like whitespace, such as a comment, a `;`, or forbidden
   characters. The whitespace around it goes too, and the whole line if
   nothing else is on it. Between two tokens it becomes a space, or a line
   break if it acted as one ([line_break]), so that the tokens stay apart.
   Every rejected sequence that lexes as whitespace is removed this way. *)
let remove_trivia cursor ~start ~stop ~line_break =
  let before = spaces_before cursor start in
  let after = skip_spaces cursor stop in
  let code_before = not (only_spaces_before cursor start) in
  let code_after = not (is_end_of_line (byte cursor after)) in
  match (code_before, code_after) with
  | true, true ->
      Diagnostic.replace (span before after)
        (if line_break then "\n" ^ indentation cursor start else " ")
  | true, false -> Diagnostic.delete (span before after)
  | false, true -> Diagnostic.delete (span start after)
  | false, false ->
      let line_start =
        max (Source.line_start cursor.source start) (Source.byte_order_mark_length cursor.source)
      in
      let stop = if byte cursor after < 0 then after else after + line_break_length cursor after in
      Diagnostic.delete (span line_start stop)

(* A run of forbidden characters starting at the cursor: one error, and the
   characters are skipped. *)
let forbidden_run cursor ~context =
  let start = cursor.position in
  let rec collect characters =
    let packed = decode cursor cursor.position in
    if packed >= 0 && Unicode.is_forbidden (Unicode.decoded_code_point packed) then begin
      cursor.position <- cursor.position + Unicode.decoded_length packed;
      collect (Unicode.decoded_code_point packed :: characters)
    end
    else List.rev characters
  in
  let characters = collect [] in
  let stop = cursor.position in
  let names = String.concat ", " (List.map describe_code_point characters) in
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
              [ Diagnostic.replace (span start stop) escapes ];
          ] )
    | Raw_string ->
        ( base
          ^ " A raw string has no escapes, so write the text as an ordinary string, with the \
             character as an escape such as `\\u{200B}`.",
          [] )
  in
  report cursor ~fixes ~code:Forbidden_character (span start stop) message

(* A run of bytes that are not valid UTF-8: one error, and they are skipped. *)
let invalid_run cursor =
  let start = cursor.position in
  while cursor.position < cursor.length && decode cursor cursor.position < 0 do
    cursor.position <- cursor.position + 1
  done;
  report cursor ~code:Invalid_utf8 (span start cursor.position)
    "Source files must be UTF-8, and these bytes are not valid UTF-8."

(* Copies the run of plain ASCII text at the cursor into [buffer] in one go:
   printable characters and tabs, up to the next byte that needs a closer
   look. [special] names the bytes the string form treats specially. *)
let copy_plain cursor buffer ~special =
  let start = cursor.position in
  let rec stop index =
    let current = byte cursor index in
    if current >= 0x20 && current < 0x7F && not (special current) then stop (index + 1)
    else if current = 0x09 then stop (index + 1)
    else index
  in
  let stop = stop start in
  if stop > start then begin
    Buffer.add_substring buffer cursor.text start (stop - start);
    cursor.position <- stop
  end

(* Reads one character of text at the cursor into [buffer], checking it. A
   forbidden or invalid character is reported and left out. *)
let read_character cursor buffer ~context =
  let packed = decode cursor cursor.position in
  if packed < 0 then invalid_run cursor
  else if Unicode.is_forbidden (Unicode.decoded_code_point packed) then
    forbidden_run cursor ~context
  else begin
    Buffer.add_substring buffer cursor.text cursor.position (Unicode.decoded_length packed);
    cursor.position <- cursor.position + Unicode.decoded_length packed
  end

(* Consumes the line break at the cursor and returns its span. A carriage
   return on its own is an error, and still a line break, so that the lines
   after it lex normally. *)
let consume_line_break cursor =
  let start = cursor.position in
  let length = line_break_length cursor start in
  if length = 1 && byte cursor start = 0x0D then
    report cursor ~code:Carriage_return
      ~fixes:
        [
          Diagnostic.fix "Replace with a line feed"
            [ Diagnostic.replace (span start (start + 1)) "\n" ];
        ]
      (span start (start + 1))
      "A carriage return is a line break only before a line feed.";
  cursor.position <- start + length;
  span start cursor.position

(* Records a line break between tokens. *)
let note_line_break cursor line_break =
  if cursor.first_line_break <> None && cursor.line_is_blank then cursor.blank_line <- true;
  if cursor.first_line_break = None then cursor.first_line_break <- Some line_break;
  cursor.line_is_blank <- true

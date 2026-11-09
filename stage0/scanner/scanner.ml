(* Bytes to raw tokens. See LEXER.md.

   The scanner is an index moving over the file's bytes. ASCII bytes are
   handled directly, and a byte of 0x80 or above starts a UTF-8 sequence,
   which is decoded strictly. Every character is checked as it is read, in
   code and in strings alike.

   Recovery from an error inside an interpolation works by abandoning the
   rest of the line: the scanner stops at the line break, sets [abandoned],
   and every enclosing construct that must end on its line (interpolations,
   ordinary strings, one-line raw strings) ends there without another error.
   The flag is cleared where a line break is legal again: between tokens,
   or in the body of a multi-line raw string. *)

open Token

type t = {
  source : Source.t;
  text : string;
  length : int;
  diagnostics : Diagnostic.Collector.t;
  mutable position : int;
  (* Trivia since the last token. *)
  mutable first_line_break : span option;
  mutable blank_line : bool;
  mutable line_is_blank : bool;
  mutable abandoned : bool;
}

let create source diagnostics =
  {
    source;
    text = Source.text source;
    length = String.length (Source.text source);
    diagnostics;
    position = Source.byte_order_mark_length source;
    first_line_break = None;
    blank_line = false;
    line_is_blank = true;
    abandoned = false;
  }

(* Interpolations may nest at most this deep. *)
let maximum_nesting = 32

let span start stop = { start; stop }

(* The byte at [index], or -1 past the end. *)
let byte scanner index =
  if index < scanner.length then Char.code (String.unsafe_get scanner.text index) else -1

let report scanner ?notes ?fixes ~code span message =
  Diagnostic.Collector.add scanner.diagnostics (Diagnostic.make ?notes ?fixes ~code span message)

let is_line_break byte = byte = 0x0A || byte = 0x0D
let is_end_of_line byte = byte < 0 || is_line_break byte
let is_space byte = byte = 0x20 || byte = 0x09
let is_digit byte = byte >= 0x30 && byte <= 0x39

let is_ascii_name_byte byte =
  (byte >= 0x61 && byte <= 0x7A) || (byte >= 0x41 && byte <= 0x5A) || is_digit byte || byte = 0x5F

(* The decoded character at [index]: [(code_point lsl 3) lor length], or -1
   for invalid UTF-8 or the end of the file. *)
let decode scanner index = if index < scanner.length then Unicode.decode scanner.text index else -1

let run_length scanner index character =
  let rec loop position = if byte scanner position = character then loop (position + 1) else position in
  loop index - index

let skip_spaces scanner index =
  let rec loop position = if is_space (byte scanner position) then loop (position + 1) else position in
  loop index

let end_of_line scanner index =
  let rec loop position = if is_end_of_line (byte scanner position) then position else loop (position + 1) in
  loop index

(* The length of the line break at [index]: 2 for a carriage return and line
   feed, 1 for either alone. *)
let line_break_length scanner index =
  if byte scanner index = 0x0D && byte scanner (index + 1) = 0x0A then 2 else 1

let quote = Char.code '"'
let dollar = Char.code '$'

(* Describing characters in messages *)

let describe_code_point value =
  match Unicode.forbidden_name value with
  | Some name -> Printf.sprintf "U+%04X %s" value name
  | None -> Printf.sprintf "U+%04X" value

let show_character scanner index =
  let packed = decode scanner index in
  if packed < 0 then Printf.sprintf "byte 0x%02X" (byte scanner index)
  else
    let value = Unicode.decoded_code_point packed in
    if value < 0x80 then Printf.sprintf "`%c`" (Char.chr value)
    else Printf.sprintf "`%s` (U+%04X)" (String.sub scanner.text index (Unicode.decoded_length packed)) value

(* Checks on the source text *)

type context = Code | Ordinary_string | Raw_string

let indentation scanner offset =
  let start = Source.line_start scanner.source offset in
  String.sub scanner.text start (skip_spaces scanner start - start)

(* The whitespace before [offset] on its line starts here. *)
let spaces_before scanner offset =
  let line_start = Source.line_start scanner.source offset in
  let rec loop position =
    if position > line_start && is_space (byte scanner (position - 1)) then loop (position - 1)
    else position
  in
  loop offset

let only_spaces_before scanner offset =
  spaces_before scanner offset = max (Source.line_start scanner.source offset)
                                   (Source.byte_order_mark_length scanner.source)

(* The edit that removes trivia: [start, stop) holds text that the scanner
   treats like whitespace, such as a comment, a `;`, or forbidden
   characters. The whitespace around it goes too, and the whole line if
   nothing else is on it. Between two tokens it becomes a space, or a line
   break if it acted as one ([line_break]), so that the tokens stay apart.
   Every rejected sequence that lexes as whitespace is removed this way. *)
let remove_trivia scanner ~start ~stop ~line_break =
  let before = spaces_before scanner start in
  let after = skip_spaces scanner stop in
  let code_before = not (only_spaces_before scanner start) in
  let code_after = not (is_end_of_line (byte scanner after)) in
  match (code_before, code_after) with
  | true, true ->
      Diagnostic.replace (span before after)
        (if line_break then "\n" ^ indentation scanner start else " ")
  | true, false -> Diagnostic.delete (span before after)
  | false, true -> Diagnostic.delete (span start after)
  | false, false ->
      let line_start = Source.line_start scanner.source start in
      let line_start = max line_start (Source.byte_order_mark_length scanner.source) in
      let stop =
        if byte scanner after < 0 then after else after + line_break_length scanner after
      in
      Diagnostic.delete (span line_start stop)

(* A run of forbidden characters starting at the current position: one
   error, and the characters are skipped. *)
let forbidden_run scanner ~context =
  let start = scanner.position in
  let rec collect characters =
    let packed = decode scanner scanner.position in
    if packed >= 0 && Unicode.is_forbidden (Unicode.decoded_code_point packed) then begin
      scanner.position <- scanner.position + Unicode.decoded_length packed;
      collect (Unicode.decoded_code_point packed :: characters)
    end
    else List.rev characters
  in
  let characters = collect [] in
  let stop = scanner.position in
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
          [ Diagnostic.fix (if plural then "Delete the characters" else "Delete the character")
              [ remove_trivia scanner ~start ~stop ~line_break:false ] ] )
    | Ordinary_string ->
        let escapes =
          String.concat "" (List.map (fun value -> Printf.sprintf "\\u{%X}" value) characters)
        in
        ( base ^ " Write it as an escape, so that it can be seen.",
          [ Diagnostic.fix ("Replace with `" ^ escapes ^ "`") [ Diagnostic.replace (span start stop) escapes ] ] )
    | Raw_string ->
        ( base
          ^ " A raw string has no escapes, so write the text as an ordinary string, with the \
             character as an escape such as `\\u{200B}`.",
          [] )
  in
  report scanner ~fixes ~code:"lexer.forbidden_character" (span start stop) message

(* A run of bytes that are not valid UTF-8: one error, and they are skipped. *)
let invalid_run scanner =
  let start = scanner.position in
  while scanner.position < scanner.length && decode scanner scanner.position < 0 do
    scanner.position <- scanner.position + 1
  done;
  report scanner ~code:"lexer.invalid_utf8" (span start scanner.position)
    "Source files must be UTF-8, and these bytes are not valid UTF-8."

(* Reads one character of text at the current position into [buffer],
   checking it. Returns false if there was no character to add, because it
   was forbidden or invalid. *)
let read_character scanner buffer ~context =
  let current = byte scanner scanner.position in
  if current < 0x80 && current >= 0x20 && current <> 0x7F || current = 0x09 then begin
    Buffer.add_char buffer (Char.chr current);
    scanner.position <- scanner.position + 1
  end
  else
    let packed = decode scanner scanner.position in
    if packed < 0 then invalid_run scanner
    else if Unicode.is_forbidden (Unicode.decoded_code_point packed) then forbidden_run scanner ~context
    else begin
      Buffer.add_substring buffer scanner.text scanner.position (Unicode.decoded_length packed);
      scanner.position <- scanner.position + Unicode.decoded_length packed
    end

(* Line breaks between tokens *)

let note_line_break scanner span =
  if scanner.first_line_break <> None && scanner.line_is_blank then scanner.blank_line <- true;
  if scanner.first_line_break = None then scanner.first_line_break <- Some span;
  scanner.line_is_blank <- true

(* Consumes the line break at the current position. A carriage return on its
   own is an error, and still a line break, so that the lines after it lex
   normally. Returns the line break's span. *)
let consume_line_break scanner =
  let start = scanner.position in
  let length = line_break_length scanner start in
  if length = 1 && byte scanner start = 0x0D then
    report scanner ~code:"lexer.carriage_return"
      ~fixes:[ Diagnostic.fix "Replace with a line feed" [ Diagnostic.replace (span start (start + 1)) "\n" ] ]
      (span start (start + 1))
      "A carriage return is a line break only before a line feed.";
  scanner.position <- start + length;
  span start scanner.position

(* Rejected sequences *)

let comment_message =
  "Truss has no comments. Say this with a name, a contract, or a test instead."

let line_comment scanner =
  let start = scanner.position in
  let stop = end_of_line scanner start in
  scanner.position <- stop;
  scanner.line_is_blank <- false;
  report scanner ~code:"lexer.comment"
    ~fixes:[ Diagnostic.fix "Remove the comment" [ remove_trivia scanner ~start ~stop ~line_break:false ] ]
    (span start stop) comment_message

let block_comment scanner =
  let start = scanner.position in
  let first_line_break = ref None in
  let rec loop depth position =
    let current = byte scanner position in
    if current < 0 then (position, false)
    else if current = Char.code '*' && byte scanner (position + 1) = Char.code '/' then
      if depth = 1 then (position + 2, true) else loop (depth - 1) (position + 2)
    else if current = Char.code '/' && byte scanner (position + 1) = Char.code '*' then
      loop (depth + 1) (position + 2)
    else begin
      if is_line_break current && !first_line_break = None then
        first_line_break := Some (span position (position + line_break_length scanner position));
      loop depth (position + 1)
    end
  in
  let stop, closed = loop 1 (start + 2) in
  scanner.position <- stop;
  scanner.line_is_blank <- false;
  (* A comment that spans lines separates the tokens around it like a line
     break. *)
  (match !first_line_break with
  | Some line_break when scanner.first_line_break = None -> scanner.first_line_break <- Some line_break
  | _ -> ());
  report scanner ~code:"lexer.comment"
    ~fixes:
      [ Diagnostic.fix "Remove the comment"
          [ remove_trivia scanner ~start ~stop ~line_break:(!first_line_break <> None) ] ]
    (span start stop)
    (if closed then comment_message else comment_message ^ " This comment is never closed.")

let semicolon scanner =
  let start = scanner.position in
  scanner.position <- start + 1;
  scanner.line_is_blank <- false;
  let rec next_code position =
    let position = skip_spaces scanner position in
    if byte scanner position = Char.code ';' then next_code (position + 1) else position
  in
  let next = next_code (start + 1) in
  (* Mid-line, the next token starts a new statement, unless it is a `}`. *)
  let line_break = not (is_end_of_line (byte scanner next) || byte scanner next = Char.code '}') in
  if line_break && scanner.first_line_break = None then
    scanner.first_line_break <- Some (span start (start + 1));
  let fix =
    Diagnostic.fix
      (if line_break then "Replace the `;` with a line break" else "Remove the `;`")
      [ remove_trivia scanner ~start ~stop:(start + 1) ~line_break ]
  in
  report scanner ~code:"lexer.semicolon" ~fixes:[ fix ] (span start (start + 1))
    "Statements end at a line break. Truss has no `;`."

let unexpected ?(code = "lexer.unexpected_character") scanner ~length message =
  let start = scanner.position in
  scanner.position <- start + length;
  scanner.line_is_blank <- false;
  report scanner ~code (span start (start + length)) message

(* The end of a character literal from another language, such as `'a'` or
   `'\n'`, that starts at [start], or -1 if there is none. *)
let character_literal_end scanner start =
  let content = start + 1 in
  let current = byte scanner content in
  let close =
    if current = Char.code '\\' then
      let escaped = byte scanner (content + 1) in
      if escaped = Char.code 'u' && byte scanner (content + 2) = Char.code '{' then
        match String.index_from_opt scanner.text (content + 3) '}' with
        | Some brace when brace - content <= 10 -> brace + 1
        | _ -> -1
      else if List.mem escaped (List.map Char.code [ 'n'; 't'; 'r'; '0'; '\\'; '"'; '\'' ]) then content + 2
      else -1
    else if current < 0 || is_line_break current || current = Char.code '\'' then -1
    else
      let packed = decode scanner content in
      if packed < 0 || Unicode.is_forbidden (Unicode.decoded_code_point packed) then -1
      else content + Unicode.decoded_length packed
  in
  if close >= 0 && byte scanner close = Char.code '\'' then close + 1 else -1

(* Whether a run of `$` at [index] opens a raw string. *)
let opens_raw_string scanner index =
  let dollars = run_length scanner index dollar in
  run_length scanner (index + dollars) quote >= 3

(* Skips everything between tokens: whitespace, line breaks, and the
   characters and sequences that are errors outside strings. Inside an
   interpolation ([inline]), it stops at a line break, and comments and `;`
   are reported without a fix, since removing them to the end of the line
   would remove the end of the string too. *)
let rec skip_trivia scanner ~inline =
  let current = byte scanner scanner.position in
  let next = byte scanner (scanner.position + 1) in
  let continue () = skip_trivia scanner ~inline in
  let inline_rejected ?code length message =
    unexpected ?code scanner ~length message;
    continue ()
  in
  if current < 0 then ()
  else if is_space current then begin
    scanner.position <- scanner.position + 1;
    continue ()
  end
  else if is_line_break current then begin
    if not inline then begin
      note_line_break scanner (consume_line_break scanner);
      continue ()
    end
  end
  else if current = Char.code '/' && (next = Char.code '/' || next = Char.code '*') then
    if inline then inline_rejected ~code:"lexer.comment" 2 comment_message
    else begin
      if next = Char.code '/' then line_comment scanner else block_comment scanner;
      continue ()
    end
  else if current = Char.code '#' then
    if inline then inline_rejected ~code:"lexer.comment" 1 comment_message
    else begin
      line_comment scanner;
      continue ()
    end
  else if current = Char.code ';' then
    if inline then inline_rejected ~code:"lexer.semicolon" 1 "Truss has no `;`."
    else begin
      semicolon scanner;
      continue ()
    end
  else if current = Char.code '@' || current = Char.code '`' || current = Char.code '\\' then
    inline_rejected 1
      (if current = Char.code '`' then "The backtick is not used in Truss."
       else Printf.sprintf "`%c` is not used in Truss." (Char.chr current))
  else if current = Char.code '\'' && character_literal_end scanner scanner.position < 0 then
    inline_rejected 1 "`'` is not used in Truss. Strings are written with `\"`."
  else if current = dollar && not (opens_raw_string scanner scanner.position) then
    inline_rejected
      (run_length scanner scanner.position dollar)
      "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s before a \
       raw string's `\"\"\"` choose how it interpolates."
  else if current < 0x20 || current = 0x7F then begin
    forbidden_run scanner ~context:Code;
    scanner.line_is_blank <- false;
    continue ()
  end
  else if current >= 0x80 then begin
    let packed = decode scanner scanner.position in
    if packed < 0 then begin
      invalid_run scanner;
      continue ()
    end
    else
      let value = Unicode.decoded_code_point packed in
      if Unicode.is_forbidden value then begin
        forbidden_run scanner ~context:Code;
        scanner.line_is_blank <- false;
        continue ()
      end
      else if not (Unicode.is_xid_start value) then
        inline_rejected (Unicode.decoded_length packed)
          (Printf.sprintf "%s is not used in Truss." (show_character scanner scanner.position))
  end

(* A multi-line raw string's body, before its indentation is removed. Each
   line has one more text piece than interpolations. *)
type raw_line = { line_start : int; line_texts : text list; line_interpolations : interpolation list }

type closing =
  | Own_line of { indentation : string; delimiter_start : int }
  | After_text of int  (* the closing delimiter's offset *)
  | Unterminated of int  (* where the string is taken to end *)

type raw_body = { lines : raw_line list; after : int; closing : closing }

(* Tokens *)

let token kind start stop =
  { kind; span = span start stop; line_break_before = false; blank_line_before = false }

let end_of_file_at position = { token = token End_of_file position position; first_line_break = None }

let rec scan_token scanner ~nesting =
  let start = scanner.position in
  let current = byte scanner start in
  let next = byte scanner (start + 1) in
  let punctuation kind length =
    scanner.position <- start + length;
    Punctuation kind
  in
  let choose options default =
    match List.find_opt (fun (character, _, _) -> next = Char.code character) options with
    | Some (_, kind, length) -> punctuation kind length
    | None -> punctuation default 1
  in
  let kind =
    if (current >= 0x61 && current <= 0x7A) || (current >= 0x41 && current <= 0x5A) || current = 0x5F || current >= 0x80
    then scan_name scanner ~nesting
    else if is_digit current then scan_number scanner
    else
      match Char.chr current with
      | '"' -> scan_string scanner ~tag:None ~nesting
      | '$' -> scan_string scanner ~tag:None ~nesting
      | '\'' -> scan_character_literal scanner
      | '(' -> punctuation Left_paren 1
      | ')' -> punctuation Right_paren 1
      | '[' -> punctuation Left_bracket 1
      | ']' -> punctuation Right_bracket 1
      | '{' -> punctuation Left_brace 1
      | '}' -> punctuation Right_brace 1
      | ',' -> punctuation Comma 1
      | '?' -> punctuation Question 1
      | '~' -> punctuation Tilde 1
      | ':' -> choose [ (':', Colon_colon, 2) ] Colon
      | '.' ->
          if next = Char.code '.' then
            if byte scanner (start + 2) = Char.code '=' then punctuation Dot_dot_equal 3
            else punctuation Dot_dot 2
          else punctuation Dot 1
      | '-' ->
          if next = Char.code '-' then begin
            scanner.position <- start + 2;
            Foreign Minus_minus
          end
          else choose [ ('>', Arrow, 2); ('=', Minus_equal, 2) ] Minus
      | '+' ->
          if next = Char.code '+' then begin
            scanner.position <- start + 2;
            Foreign Plus_plus
          end
          else choose [ ('=', Plus_equal, 2) ] Plus
      | '*' -> choose [ ('=', Star_equal, 2) ] Star
      | '/' -> choose [ ('=', Slash_equal, 2) ] Slash
      | '%' -> choose [ ('=', Percent_equal, 2) ] Percent
      | '^' -> choose [ ('=', Caret_equal, 2) ] Caret
      | '&' -> choose [ ('&', And_and, 2); ('=', Ampersand_equal, 2) ] Ampersand
      | '|' -> choose [ ('|', Or_or, 2); ('=', Bar_equal, 2) ] Bar
      | '=' | '!' when next = Char.code '=' && byte scanner (start + 2) = Char.code '=' ->
          let written, replacement, kind =
            if current = Char.code '=' then ("===", "==", Equal_equal) else ("!==", "!=", Not_equal)
          in
          report scanner ~code:"lexer.strict_equality"
            ~fixes:[ Diagnostic.fix ("Write `" ^ replacement ^ "`") [ Diagnostic.replace (span start (start + 3)) replacement ] ]
            (span start (start + 3))
            (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written replacement);
          punctuation kind 3
      | '=' when next = Char.code '=' && byte scanner (start + 2) = Char.code '>' -> punctuation Implies 3
      | '=' -> choose [ ('=', Equal_equal, 2); ('>', Fat_arrow, 2) ] Equal
      | '!' -> choose [ ('=', Not_equal, 2) ] Bang
      | '<' ->
          if next = Char.code '<' then
            if byte scanner (start + 2) = Char.code '=' then punctuation Shift_left_equal 3
            else punctuation Shift_left 2
          else choose [ ('=', Less_equal, 2) ] Less
      | '>' ->
          if next = Char.code '>' then
            if byte scanner (start + 2) = Char.code '=' then punctuation Shift_right_equal 3
            else punctuation Shift_right 2
          else choose [ ('=', Greater_equal, 2) ] Greater
      | _ -> invalid_arg "Scanner.scan_token: no token here"
  in
  token kind start scanner.position

(* Names *)

and scan_name scanner ~nesting =
  let start = scanner.position in
  let rec loop () =
    let current = byte scanner scanner.position in
    if current >= 0 && current < 0x80 then begin
      if is_ascii_name_byte current then begin
        scanner.position <- scanner.position + 1;
        loop ()
      end
    end
    else
      let packed = decode scanner scanner.position in
      if packed >= 0 && Unicode.is_xid_continue (Unicode.decoded_code_point packed) then begin
        scanner.position <- scanner.position + Unicode.decoded_length packed;
        loop ()
      end
  in
  loop ();
  let stop = scanner.position in
  let name = String.sub scanner.text start (stop - start) in
  let kind =
    if name = "_" then Underscore
    else
      match Token.word name with
      | Some kind -> kind
      | None -> (
              let checked = Names.check name in
              (match checked.problem with
              | Some (code, message) ->
                  let fixes =
                    match checked.fix with
                    | Some fixed ->
                        [ Diagnostic.fix ("Write `" ^ fixed ^ "`") [ Diagnostic.replace (span start stop) fixed ] ]
                    | None -> []
                  in
                  report scanner ~code ~fixes (span start stop) message
              | None -> ());
              if checked.kind = Names.Upper then Upper checked.name else Lower checked.name)
  in
  (* An UpperCamelCase name touching a string is the string's tag. *)
  match kind with
  | Upper tag
    when byte scanner stop = quote
         || (byte scanner stop = dollar && opens_raw_string scanner stop) ->
      let literal = scan_string scanner ~tag:(Some (tag, span start stop)) ~nesting in
      literal
  | kind -> kind

(* Numbers *)

and scan_number scanner =
  let start = scanner.position in
  let stop = Numbers.scan_end scanner.text start in
  scanner.position <- stop;
  let checked = Numbers.check (String.sub scanner.text start (stop - start)) in
  (match checked.problem with
  | Some problem ->
      report scanner ~code:problem.code
        ~fixes:
          (List.map
             (fun (title, replacement) -> Diagnostic.fix title [ Diagnostic.replace (span start stop) replacement ])
             checked.fixes)
        (span (start + problem.start) (start + problem.stop))
        problem.message
  | None -> ());
  match checked.value with
  | Numbers.Integer value -> Integer value
  | Numbers.Float { significand; exponent } -> Float { significand; exponent }

(* Strings *)

(* The text pieces and interpolations of a string, as they are read. *)
and pieces start = (ref [], ref [], Buffer.create 32, ref start)

and flush (texts, _, buffer, text_start) stop =
  texts := { value = Buffer.contents buffer; span = span !text_start stop } :: !texts;
  Buffer.clear buffer

and add_interpolation ((_, interpolations, _, text_start) as pieces) interpolation =
  flush pieces interpolation.span.start;
  interpolations := interpolation :: !interpolations;
  text_start := interpolation.span.stop

and literal ~tag ~form (texts, interpolations, _, _) =
  String
    {
      tag;
      form;
      texts = Array.of_list (List.rev !texts);
      interpolations = Array.of_list (List.rev !interpolations);
    }

(* At a run of quotes, or of dollar signs before a raw string. *)
and scan_string scanner ~tag ~nesting =
  let start = scanner.position in
  let dollars = run_length scanner start dollar in
  let quotes = run_length scanner (start + dollars) quote in
  if dollars = 0 && quotes = 1 then scan_ordinary scanner ~tag ~nesting
  else if dollars = 0 && quotes = 2 then begin
    scanner.position <- start + 2;
    String
      {
        tag;
        form = Ordinary;
        texts = [| { value = ""; span = span (start + 1) (start + 1) } |];
        interpolations = [||];
      }
  end
  else scan_raw scanner ~tag ~nesting ~dollars ~quotes

and scan_ordinary scanner ~tag ~nesting =
  let open_quote = scanner.position in
  let literal_start = match tag with Some (_, tag_span) -> tag_span.start | None -> open_quote in
  scanner.position <- open_quote + 1;
  let ((_, _, buffer, _) as pieces) = pieces scanner.position in
  let rec loop () =
    let current = byte scanner scanner.position in
    if scanner.abandoned then flush pieces scanner.position
    else if is_end_of_line current then begin
      flush pieces scanner.position;
      let message =
        "This string is not closed on its line. An ordinary string fits on one line; text that \
         spans lines goes in a raw string, between `\"\"\"`s."
      in
      if nesting = 0 then
        report scanner ~code:"lexer.unterminated_string"
          ~fixes:[ Diagnostic.fix "Close the string" [ Diagnostic.insert scanner.position "\"" ] ]
          (span literal_start scanner.position) message
      else begin
        report scanner ~code:"lexer.unterminated_string" (span literal_start scanner.position) message;
        scanner.abandoned <- true
      end
    end
    else if current = quote then begin
      flush pieces scanner.position;
      scanner.position <- scanner.position + 1
    end
    else if current = Char.code '\\' then
      if scan_escape scanner buffer ~nesting then loop () else flush pieces scanner.position
    else if current = dollar && byte scanner (scanner.position + 1) = Char.code '{' then begin
      add_interpolation pieces (scan_interpolation scanner ~nesting ~delimiter_length:2);
      loop ()
    end
    else begin
      read_character scanner buffer ~context:Ordinary_string;
      loop ()
    end
  in
  loop ();
  literal ~tag ~form:Ordinary pieces

(* An escape in an ordinary string, at its `\`. Returns false when the
   string ends here, after a `\` at the end of a line. *)
and scan_escape scanner buffer ~nesting =
  let start = scanner.position in
  let escaped = byte scanner (start + 1) in
  let simple value =
    Buffer.add_char buffer value;
    scanner.position <- start + 2;
    true
  in
  let escapes = "The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, `\\\"`, `\\${`, and `\\u{...}`." in
  match if escaped < 0 then '\000' else Char.chr escaped with
  | _ when is_end_of_line escaped ->
      report scanner ~code:"lexer.invalid_escape" (span start (start + 1))
        "A `\\` at the end of a line does not continue the string. Text that spans lines goes in a \
         raw string, between `\"\"\"`s.";
      scanner.position <- start + 1;
      if nesting > 0 then scanner.abandoned <- true;
      false
  | 'n' -> simple '\n'
  | 't' -> simple '\t'
  | 'r' -> simple '\r'
  | '0' -> simple '\000'
  | '\\' -> simple '\\'
  | '"' -> simple '"'
  | '$' when byte scanner (start + 2) = Char.code '{' ->
      Buffer.add_string buffer "${";
      scanner.position <- start + 3;
      true
  | 'u' ->
      let problem stop message =
        report scanner ~code:"lexer.invalid_escape" (span start stop) message;
        scanner.position <- stop;
        true
      in
      let form = "A Unicode escape is written `\\u{...}`, with 1 to 6 hexadecimal digits." in
      if byte scanner (start + 2) <> Char.code '{' then problem (start + 2) form
      else
        let digits_start = start + 3 in
        let rec digits_end position =
          let current = byte scanner position in
          if is_digit current || (current >= 0x61 && current <= 0x66) || (current >= 0x41 && current <= 0x46)
          then digits_end (position + 1)
          else position
        in
        let stop = digits_end digits_start in
        let count = stop - digits_start in
        if byte scanner stop <> Char.code '}' then problem stop form
        else if count = 0 || count > 6 then problem (stop + 1) form
        else
          let value = int_of_string ("0x" ^ String.sub scanner.text digits_start count) in
          if value > 0x10FFFF || (value >= 0xD800 && value <= 0xDFFF) then
            problem (stop + 1)
              (Printf.sprintf "`\\u{%s}` is not a Unicode scalar value: surrogates and values above \
                               10FFFF have no character."
                 (String.sub scanner.text digits_start count))
          else begin
            Unicode.encode buffer value;
            scanner.position <- stop + 1;
            true
          end
  | _ ->
      let packed = decode scanner (start + 1) in
      let length = if packed < 0 then 1 else Unicode.decoded_length packed in
      let written = String.sub scanner.text start (1 + length) in
      report scanner ~code:"lexer.invalid_escape" (span start (start + 1 + length))
        (Printf.sprintf "`%s` is not an escape. %s" written escapes);
      scanner.position <- start + 1 + length;
      true

(* An interpolation, at its delimiter: `${`, or the `$`s and `{` of a raw
   string opened with `$`s. *)
and scan_interpolation scanner ~nesting ~delimiter_length =
  let start = scanner.position in
  if nesting + 1 > maximum_nesting then begin
    report scanner ~code:"lexer.interpolation_too_deep" (span start (start + delimiter_length))
      (Printf.sprintf "Interpolations can nest at most %d deep." maximum_nesting);
    scanner.position <- end_of_line scanner start;
    scanner.abandoned <- true;
    { tokens = [| token End_of_file scanner.position scanner.position |]; span = span start scanner.position }
  end
  else begin
    scanner.position <- start + delimiter_length;
    let braces = ref 0 in
    let finished = ref false in
    let closed = ref false in
    let count = ref 0 in
    let pull () =
      if !finished || scanner.abandoned then begin
        finished := true;
        end_of_file_at scanner.position
      end
      else begin
        skip_trivia scanner ~inline:true;
        let current = byte scanner scanner.position in
        if is_end_of_line current then begin
          report scanner ~code:"lexer.line_break_in_interpolation" (span start scanner.position)
            "An interpolation cannot contain a line break. Move the expression into a `let` before \
             the string.";
          scanner.abandoned <- true;
          finished := true;
          end_of_file_at scanner.position
        end
        else if current = Char.code '}' && !braces = 0 then begin
          scanner.position <- scanner.position + 1;
          finished := true;
          closed := true;
          end_of_file_at (scanner.position - 1)
        end
        else begin
          let token = scan_token scanner ~nesting:(nesting + 1) in
          (match token.kind with
          | Punctuation Left_brace -> incr braces
          | Punctuation Right_brace -> decr braces
          | _ -> ());
          incr count;
          { token; first_line_break = None }
        end
      end
    in
    let tokens =
      match
        Layout.run ~source:scanner.source ~diagnostics:scanner.diagnostics
          ~mode:(Layout.Interpolation { cut_off = (fun () -> not !closed) })
          pull
      with
      | Some tokens -> tokens
      | None -> assert false
    in
    let interpolation_span = span start scanner.position in
    if !closed && !count = 0 then
      report scanner ~code:"lexer.empty_interpolation"
        ~fixes:[ Diagnostic.fix "Remove the empty interpolation" [ Diagnostic.delete interpolation_span ] ]
        interpolation_span "An interpolation needs an expression.";
    { tokens; span = interpolation_span }
  end

(* At the dollar signs or quotes that open a raw string. *)
and scan_raw scanner ~tag ~nesting ~dollars ~quotes =
  let delimiter_start = scanner.position in
  let literal_start = match tag with Some (_, tag_span) -> tag_span.start | None -> delimiter_start in
  let after = delimiter_start + dollars + quotes in
  let line_end = end_of_line scanner after in
  let multi_line = skip_spaces scanner after = line_end in
  let form = Raw { quotes; dollars; multi_line } in
  if not multi_line then begin
    scanner.position <- after;
    scan_one_line_raw scanner ~tag ~form ~nesting ~literal_start ~dollars ~quotes
  end
  else if nesting > 0 then begin
    report scanner ~code:"lexer.line_break_in_interpolation" (span literal_start line_end)
      "An interpolation cannot contain a line break, so it cannot hold a multi-line string. Move \
       the expression into a `let` before the string.";
    scanner.position <- line_end;
    scanner.abandoned <- true;
    let empty = pieces after in
    flush empty after;
    literal ~tag ~form empty
  end
  else scan_multi_line_raw scanner ~tag ~form ~literal_start ~dollars ~quotes ~after ~line_end

(* Reads a run of `$` in a raw string's body: either text, or the start of an
   interpolation, which a run of at least max(n, 1) `$`s followed by `{`
   begins. The first `$`s of a longer run are text. *)
and raw_dollars scanner ((_, _, buffer, _) as pieces) ~dollars ~nesting =
  let start = scanner.position in
  let run = run_length scanner start dollar in
  let needed = max dollars 1 in
  if run >= needed && byte scanner (start + run) = Char.code '{' then begin
    Buffer.add_string buffer (String.make (run - needed) '$');
    scanner.position <- start + run - needed;
    add_interpolation pieces (scan_interpolation scanner ~nesting ~delimiter_length:(needed + 1))
  end
  else begin
    Buffer.add_string buffer (String.make run '$');
    scanner.position <- start + run
  end

and too_many_quotes scanner ~start ~run ~quotes ~multi_line =
  report scanner ~code:"lexer.raw_string_quotes" (span start (start + run))
    (Printf.sprintf
       "A run of %d `\"`s is longer than this string's delimiter of %d.%s" run quotes
       (if multi_line then " Open the string with a longer delimiter."
        else
          " A one-line raw string cannot start or end with `\"`; use the multi-line form, or a \
           longer delimiter."))

and scan_one_line_raw scanner ~tag ~form ~nesting ~literal_start ~dollars ~quotes =
  let ((_, _, buffer, _) as pieces) = pieces scanner.position in
  let delimiter = String.make quotes '"' in
  let rec loop () =
    let current = byte scanner scanner.position in
    if scanner.abandoned then flush pieces scanner.position
    else if is_end_of_line current then begin
      flush pieces scanner.position;
      let message =
        Printf.sprintf
          "This raw string is not closed on its line. A raw string with text after its opening \
           `%s` is a one-line string. For several lines, start the text on the line after the \
           opening `%s`."
          delimiter delimiter
      in
      let fixes =
        if nesting = 0 && byte scanner (scanner.position - 1) <> quote then
          [ Diagnostic.fix ("Close the string with `" ^ delimiter ^ "`") [ Diagnostic.insert scanner.position delimiter ] ]
        else []
      in
      report scanner ~code:"lexer.unterminated_string" ~fixes (span literal_start scanner.position) message;
      if nesting > 0 then scanner.abandoned <- true
    end
    else if current = quote then begin
      let start = scanner.position in
      let run = run_length scanner start quote in
      if run >= quotes then begin
        flush pieces start;
        if run > quotes then too_many_quotes scanner ~start ~run ~quotes ~multi_line:false;
        scanner.position <- start + run
      end
      else begin
        Buffer.add_string buffer (String.make run '"');
        scanner.position <- start + run;
        loop ()
      end
    end
    else if current = dollar then begin
      raw_dollars scanner pieces ~dollars ~nesting;
      loop ()
    end
    else begin
      read_character scanner buffer ~context:Raw_string;
      loop ()
    end
  in
  loop ();
  literal ~tag ~form pieces

(* A multi-line raw string's body is read line by line. Each line keeps its
   pieces, so that the indentation can be removed once the closing line is
   found. *)
and scan_multi_line_raw scanner ~tag ~form ~literal_start ~dollars ~quotes ~after ~line_end =
  let mark = Diagnostic.Collector.mark scanner.diagnostics in
  match read_raw_lines scanner ~dollars ~quotes ~after ~line_end ~limit:None with
  | `Closed body -> build_multi_line scanner ~tag ~form ~quotes body
  | `Unterminated _ ->
      (* Guess where the string was meant to end, and read it again up to
         there, so that what follows lexes as code. *)
      Diagnostic.Collector.reset scanner.diagnostics mark;
      scanner.abandoned <- false;
      let guess = guess_raw_string_end scanner ~literal_start ~line_end in
      let body =
        match read_raw_lines scanner ~dollars ~quotes ~after ~line_end ~limit:guess with
        | `Closed body | `Unterminated body -> body
      in
      let indentation = common_indentation body.lines in
      let delimiter = String.make quotes '"' in
      let position = scanner.position in
      let insertion =
        let ends_with_line_break = position > 0 && is_line_break (byte scanner (position - 1)) in
        if ends_with_line_break || position = 0 then indentation ^ delimiter ^ "\n"
        else "\n" ^ indentation ^ delimiter
      in
      (* The string ends at the start of a line, so the token after it
         starts a new line. *)
      (if guess <> None && scanner.first_line_break = None then
         let line_break_start =
           if position >= 2 && byte scanner (position - 2) = 0x0D && byte scanner (position - 1) = 0x0A
           then position - 2
           else position - 1
         in
         scanner.first_line_break <- Some (span line_break_start position));
      report scanner ~code:"lexer.unterminated_string"
        ~fixes:[ Diagnostic.fix ("Close the string with `" ^ delimiter ^ "`") [ Diagnostic.insert position insertion ] ]
        (span literal_start after)
        (Printf.sprintf
           "This raw string is never closed. Close it with `%s` on a line of its own%s." delimiter
           (match guess with
           | Some _ -> ", before the line where it seems to end"
           | None -> ""));
      build_multi_line scanner ~tag ~form ~quotes { body with closing = Unterminated position }

and read_raw_lines scanner ~dollars ~quotes ~after ~line_end ~limit =
  scanner.position <- line_end;
  if scanner.position < scanner.length then ignore (consume_line_break scanner);
  let lines = ref [] in
  let finish closing = { lines = List.rev !lines; after; closing } in
  let rec line () =
    let line_start = scanner.position in
    let past_limit = match limit with Some limit -> line_start >= limit | None -> false in
    if past_limit || line_start >= scanner.length then `Unterminated (finish (Unterminated line_start))
    else
      let first = skip_spaces scanner line_start in
      if byte scanner first = quote && run_length scanner first quote >= quotes then begin
        let run = run_length scanner first quote in
        if run > quotes then too_many_quotes scanner ~start:first ~run ~quotes ~multi_line:true;
        scanner.position <- first + run;
        `Closed
          (finish
             (Own_line
                { indentation = String.sub scanner.text line_start (first - line_start); delimiter_start = first }))
      end
      else
        let ((_, _, buffer, _) as pieces) = pieces line_start in
        let record () =
          let texts, interpolations, _, _ = pieces in
          lines :=
            {
              line_start;
              line_texts = List.rev !texts;
              line_interpolations = List.rev !interpolations;
            }
            :: !lines
        in
        let rec content () =
          let current = byte scanner scanner.position in
          if scanner.abandoned then begin
            scanner.abandoned <- false;
            content ()
          end
          else if is_end_of_line current then begin
            flush pieces scanner.position;
            record ();
            if current < 0 then `Unterminated (finish (Unterminated scanner.position))
            else begin
              ignore (consume_line_break scanner);
              line ()
            end
          end
          else if current = quote then begin
            let start = scanner.position in
            let run = run_length scanner start quote in
            if run = quotes then begin
              flush pieces start;
              record ();
              scanner.position <- start + run;
              `Closed (finish (After_text start))
            end
            else begin
              (* A longer run after text is an error, and is kept as text. *)
              if run > quotes then too_many_quotes scanner ~start ~run ~quotes ~multi_line:true;
              Buffer.add_string buffer (String.make run '"');
              scanner.position <- start + run;
              content ()
            end
          end
          else if current = dollar then begin
            raw_dollars scanner pieces ~dollars ~nesting:0;
            content ()
          end
          else begin
            read_character scanner buffer ~context:Raw_string;
            content ()
          end
        in
        content ()
  in
  line ()

(* The longest run of whitespace that starts every line holding more than
   whitespace. *)
and common_indentation lines =
  let leading line =
    match line.line_texts with
    | first :: _ ->
        let value = first.value in
        let rec count index =
          if index < String.length value && (value.[index] = ' ' || value.[index] = '\t') then count (index + 1)
          else index
        in
        let length = count 0 in
        if length = String.length value && line.line_interpolations = [] then None
        else Some (String.sub value 0 length)
    | [] -> None
  in
  let common first second =
    let length = min (String.length first) (String.length second) in
    let rec loop index = if index < length && first.[index] = second.[index] then loop (index + 1) else index in
    String.sub first 0 (loop 0)
  in
  List.fold_left
    (fun common_so_far line ->
      match (leading line, common_so_far) with
      | None, _ -> common_so_far
      | Some prefix, None -> Some prefix
      | Some prefix, Some so_far -> Some (common prefix so_far))
    None lines
  |> Option.value ~default:""

(* Where an unterminated multi-line raw string probably ends: before the
   first non-blank line indented less than the line holding the opening
   delimiter, or before the first line that starts with a definition keyword
   in column 0. *)
and guess_raw_string_end scanner ~literal_start ~line_end =
  let opener_line = Source.line_start scanner.source literal_start in
  let opener_indentation = skip_spaces scanner opener_line - opener_line in
  let rec search position =
    if position >= scanner.length then None
    else
      let line_start = position + line_break_length scanner position in
      if line_start >= scanner.length then None
      else
        let first = skip_spaces scanner line_start in
        let blank = is_end_of_line (byte scanner first) in
        let word_end =
          let rec loop index = if is_ascii_name_byte (byte scanner index) then loop (index + 1) else index in
          loop line_start
        in
        let starts_definition =
          word_end > line_start
          &&
          match Token.word (String.sub scanner.text line_start (word_end - line_start)) with
          | Some (Keyword keyword) -> List.mem keyword definition_keywords
          | _ -> false
        in
        if ((not blank) && first - line_start < opener_indentation) || starts_definition then Some line_start
        else search (end_of_line scanner line_start)
  in
  search line_end

(* Removes the indentation and joins the lines. *)
and build_multi_line scanner ~tag ~form ~quotes body =
  let indentation, delimiter_start =
    match body.closing with
    | Own_line { indentation; delimiter_start } -> (indentation, delimiter_start)
    | After_text start ->
        let indentation = common_indentation body.lines in
        report scanner ~code:"lexer.raw_string_closing_not_alone"
          ~fixes:[ Diagnostic.fix "Move the closing delimiter to its own line" [ Diagnostic.insert start ("\n" ^ indentation) ] ]
          (span start (start + quotes))
          "The closing delimiter of a multi-line raw string goes on a line of its own.";
        (indentation, start)
    | Unterminated position -> (common_indentation body.lines, position)
  in
  let show whitespace =
    if whitespace = "" then "no indentation"
    else
      let rec groups index =
        if index >= String.length whitespace then []
        else
          let character = whitespace.[index] in
          let rec stop position =
            if position < String.length whitespace && whitespace.[position] = character then stop (position + 1)
            else position
          in
          let next = stop index in
          let count = next - index in
          let name = if character = '\t' then "tab" else "space" in
          Printf.sprintf "%d %s%s" count name (if count = 1 then "" else "s") :: groups next
      in
      String.concat " then " (groups 0)
  in
  let texts = ref [] and interpolations = ref [] in
  let buffer = Buffer.create 64 in
  let text_start = ref body.after in
  List.iteri
    (fun index line ->
      if index > 0 then Buffer.add_char buffer '\n';
      let first, rest = match line.line_texts with first :: rest -> (first, rest) | [] -> assert false in
      let value = first.value in
      let whitespace_only =
        line.line_interpolations = [] && String.for_all (fun c -> c = ' ' || c = '\t') value
      in
      let stripped =
        if String.starts_with ~prefix:indentation value then
          String.sub value (String.length indentation) (String.length value - String.length indentation)
        else if whitespace_only then ""
        else begin
          let length = min (String.length value) (String.length indentation) in
          let rec differs index =
            if index < length && value.[index] = indentation.[index] then differs (index + 1) else index
          in
          let at = differs 0 in
          let line_whitespace =
            let rec count index =
              if index < String.length value && (value.[index] = ' ' || value.[index] = '\t') then count (index + 1)
              else index
            in
            String.sub value 0 (count 0)
          in
          report scanner ~code:"lexer.raw_string_indentation"
            (span (first.span.start + at) (first.span.start + at + 1))
            (Printf.sprintf
               "Every line of a multi-line raw string starts with the indentation of its closing \
                delimiter, which is %s. This line starts with %s."
               (show indentation) (show line_whitespace));
          String.sub value at (String.length value - at)
        end
      in
      Buffer.add_string buffer stripped;
      (* The line's other pieces alternate with its interpolations. *)
      List.iteri
        (fun piece_index interpolation ->
          texts := { value = Buffer.contents buffer; span = span !text_start interpolation.span.start } :: !texts;
          Buffer.clear buffer;
          interpolations := interpolation :: !interpolations;
          text_start := interpolation.span.stop;
          Buffer.add_string buffer (List.nth rest piece_index).value)
        line.line_interpolations)
    body.lines;
  texts := { value = Buffer.contents buffer; span = span !text_start delimiter_start } :: !texts;
  String
    {
      tag;
      form;
      texts = Array.of_list (List.rev !texts);
      interpolations = Array.of_list (List.rev !interpolations);
    }

(* Character literals from other languages *)

and scan_character_literal scanner =
  let start = scanner.position in
  let stop = character_literal_end scanner start in
  let content = String.sub scanner.text (start + 1) (stop - start - 2) in
  let as_ordinary =
    match content with "\"" -> "\\\"" | "\\'" -> "'" | other -> other
  in
  let value =
    match content with
    | "\\n" -> "\n" | "\\t" -> "\t" | "\\r" -> "\r" | "\\0" -> "\000" | "\\\\" -> "\\"
    | "\\\"" -> "\"" | "\\'" -> "'"
    | escape when String.starts_with ~prefix:"\\u{" escape -> (
        match int_of_string_opt ("0x" ^ String.sub escape 3 (String.length escape - 4)) with
        | Some value when value <= 0x10FFFF && (value < 0xD800 || value > 0xDFFF) ->
            Unicode.of_code_points [ value ]
        | _ -> "")
    | other -> other
  in
  let replacement = "Character\"" ^ as_ordinary ^ "\"" in
  report scanner ~code:"lexer.character_literal"
    ~fixes:[ Diagnostic.fix ("Write `" ^ replacement ^ "`") [ Diagnostic.replace (span start stop) replacement ] ]
    (span start stop)
    (Printf.sprintf "Truss has no character literals. A single character is a tagged string: `%s`." replacement);
  scanner.position <- stop;
  String
    {
      tag = Some ("Character", span start start);
      form = Ordinary;
      texts = [| { value; span = span (start + 1) (stop - 1) } |];
      interpolations = [||];
    }

(* The next raw token of the file. *)
let next scanner =
  scanner.abandoned <- false;
  skip_trivia scanner ~inline:false;
  let first_line_break = scanner.first_line_break in
  let blank_line = scanner.blank_line in
  scanner.first_line_break <- None;
  scanner.blank_line <- false;
  let token =
    if scanner.position >= scanner.length then token End_of_file scanner.length scanner.length
    else scan_token scanner ~nesting:0
  in
  scanner.line_is_blank <- false;
  {
    token = { token with line_break_before = first_line_break <> None; blank_line_before = blank_line };
    first_line_break;
  }

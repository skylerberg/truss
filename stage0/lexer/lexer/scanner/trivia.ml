(* The sequences from other languages that lex as whitespace: comments, `;`,
   and characters Truss does not use. Each is reported, and its fix removes
   it with [Source_text.remove_trivia]. *)

open Cursor

let comment_message = "Truss has no comments. Say this with a name, a contract, or a test instead."

let line_comment cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Comment
    ~fixes:
      [
        Diagnostic.fix "Remove the comment"
          [ Source_text.remove_trivia cursor ~start ~stop ~line_break:false ];
      ]
    (span start stop) comment_message

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
  (* An unterminated comment runs to the end of the file. Removing it would
     remove the rest of the file, and where its `*/` was meant to go cannot
     be known, so it has no fix. *)
  let fixes =
    if closed then
      [
        Diagnostic.fix "Remove the comment"
          [ Source_text.remove_trivia cursor ~start ~stop ~line_break:(!first_line_break <> None) ];
      ]
    else []
  in
  report cursor ~code:Comment ~fixes (span start stop)
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

(* Reports and skips [length] bytes that cannot start a token. *)
let reject ?(code = Diagnostic.Code.Unexpected_character) cursor ~length message =
  let start = cursor.position in
  cursor.position <- start + length;
  cursor.line_is_blank <- false;
  report cursor ~code (span start (start + length)) message

(* The end of a character literal from another language, such as `'a'` or
   `'\n'`, that starts at [start], or [None] if there is none there. The
   habit is a literal that touches no name, so the quotes in
   `value's'debug` are not one. With [after_prefix], the literal follows a
   prefix, as in `b'a'`, which is the one name it may touch. *)
let character_literal_end ?(after_prefix = false) cursor start =
  let touches_name index =
    let current = byte cursor index in
    is_ascii_name_byte current || current >= 0x80
  in
  if (not after_prefix) && start > 0 && touches_name (start - 1) then None
  else
    let content = start + 1 in
    let current = byte cursor content in
    let close =
      if current = Char.code '\\' then
        let escaped = byte cursor (content + 1) in
        if escaped = Char.code 'u' && byte cursor (content + 2) = Char.code '{' then
          match String.index_from_opt cursor.text (content + 3) '}' with
          | Some brace when brace - content <= 10 -> Some (brace + 1)
          | _ -> None
        else if List.mem escaped (List.map Char.code [ 'n'; 't'; 'r'; '0'; '\\'; '"'; '\'' ]) then
          Some (content + 2)
        else None
      else if is_end_of_line current || current = Char.code '\'' then None
      else
        let packed = decode cursor content in
        if packed < 0 || Unicode.is_forbidden (Unicode.decoded_code_point packed) then None
        else Some (content + Unicode.decoded_length packed)
    in
    match close with
    | Some close when byte cursor close = Char.code '\'' && not (touches_name (close + 1)) ->
        Some (close + 1)
    | _ -> None

(* Whether the token before [index] can end an operand: a name, a literal, a
   closer, `?`, or one of the keywords that are expressions. It is read
   from the text, since the scanner does not keep the token before. *)
let after_operand cursor index =
  let rec back position =
    if position < Source.line_start cursor.source 0 then None
    else
      let current = byte cursor position in
      if is_space current || is_line_break current then back (position - 1) else Some position
  in
  match back (index - 1) with
  | None -> false
  | Some last ->
      let current = byte cursor last in
      if is_ascii_name_byte current then begin
        let rec word_start position =
          if position > 0 && is_ascii_name_byte (byte cursor (position - 1)) then
            word_start (position - 1)
          else position
        in
        let first = word_start last in
        match Token.word (String.sub cursor.text first (last + 1 - first)) with
        | Some (Keyword (True | False | Self_value | Self_type | Todo | Unreachable)) | None -> true
        | Some _ -> false
      end
      else current >= 0x80 || List.mem (Char.chr current) [ '"'; ')'; ']'; '}'; '?' ]

(* Whether an operand starts at [index], after spaces: a name, a literal, or
   an opening `(` or `[`. *)
let before_operand cursor index =
  let current = byte cursor (skip_spaces cursor index) in
  is_ascii_name_byte current || current >= 0x80
  || (current >= 0 && List.mem (Char.chr current) [ '"'; '('; '[' ])

(* An attribute of Rust, `#[derive(...)]` or `#![...]`: like a comment, it
   lexes as nothing, up to the end of its line. *)
let attribute cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Attribute
    ~fixes:
      [
        Diagnostic.fix "Remove the attribute"
          [ Source_text.remove_trivia cursor ~start ~stop ~line_break:false ];
      ]
    (span start stop)
    "Truss has no attributes. A type lists the traits it derives in a `derives` clause, and a test \
     is a `test` definition."

(* Whether a run of `$` at [index] opens a raw string. *)
let opens_raw_string cursor index =
  let dollars = run_length cursor index dollar in
  run_length cursor (index + dollars) quote >= 3

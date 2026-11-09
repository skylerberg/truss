(* The sequences from other languages that lex as whitespace: comments, `;`,
   and characters Truss does not use (LEXER.md, "Rejected sequences"). Each
   is reported, and its fix removes it with [Source_text.remove_trivia]. *)

open Cursor

let comment_message = "Truss has no comments. Say this with a name, a contract, or a test instead."

let line_comment cursor =
  let start = cursor.position in
  let stop = end_of_line cursor start in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  report cursor ~code:Comment
    ~fixes:[ Diagnostic.fix "Remove the comment" [ Source_text.remove_trivia cursor ~start ~stop ~line_break:false ] ]
    (span start stop) comment_message

let block_comment cursor =
  let start = cursor.position in
  let first_line_break = ref None in
  let rec loop depth position =
    let current = byte cursor position in
    if current < 0 then (position, false)
    else if current = Char.code '*' && byte cursor (position + 1) = Char.code '/' then
      if depth = 1 then (position + 2, true) else loop (depth - 1) (position + 2)
    else if current = Char.code '/' && byte cursor (position + 1) = Char.code '*' then loop (depth + 1) (position + 2)
    else begin
      if is_line_break current && !first_line_break = None then
        first_line_break := Some (span position (position + line_break_length cursor position));
      loop depth (position + 1)
    end
  in
  let stop, closed = loop 1 (start + 2) in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  (* A comment that spans lines separates the tokens around it like a line
     break. *)
  (match !first_line_break with
  | Some line_break when cursor.first_line_break = None -> cursor.first_line_break <- Some line_break
  | _ -> ());
  report cursor ~code:Comment
    ~fixes:
      [
        Diagnostic.fix "Remove the comment"
          [ Source_text.remove_trivia cursor ~start ~stop ~line_break:(!first_line_break <> None) ];
      ]
    (span start stop)
    (if closed then comment_message else comment_message ^ " This comment is never closed.")

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
  if line_break && cursor.first_line_break = None then cursor.first_line_break <- Some (span start (start + 1));
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
   `'\n'`, that starts at [start], or [None] if there is none there. *)
let character_literal_end cursor start =
  let content = start + 1 in
  let current = byte cursor content in
  let close =
    if current = Char.code '\\' then
      let escaped = byte cursor (content + 1) in
      if escaped = Char.code 'u' && byte cursor (content + 2) = Char.code '{' then
        match String.index_from_opt cursor.text (content + 3) '}' with
        | Some brace when brace - content <= 10 -> Some (brace + 1)
        | _ -> None
      else if List.mem escaped (List.map Char.code [ 'n'; 't'; 'r'; '0'; '\\'; '"'; '\'' ]) then Some (content + 2)
      else None
    else if is_end_of_line current || current = Char.code '\'' then None
    else
      let packed = decode cursor content in
      if packed < 0 || Unicode.is_forbidden (Unicode.decoded_code_point packed) then None
      else Some (content + Unicode.decoded_length packed)
  in
  match close with Some close when byte cursor close = Char.code '\'' -> Some (close + 1) | _ -> None

(* Whether a run of `$` at [index] opens a raw string. *)
let opens_raw_string cursor index =
  let dollars = run_length cursor index dollar in
  run_length cursor (index + dollars) quote >= 3

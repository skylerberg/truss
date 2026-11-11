(* Bytes to raw tokens.

   The scanner is an index moving over the file's bytes. ASCII bytes are
   handled directly, and a byte of 0x80 or above starts a UTF-8 sequence,
   which is decoded strictly.

   [scan] looks at each position once and decides there whether it holds
   trivia, which it skips, or the start of a token, which it reads. There is
   no second place that must agree with it about where tokens start. *)

open Token
open Cursor

type t = Cursor.t

let create = Cursor.create

(* The punctuation that starts with [current], by longest match, or [None]
   if [current] starts none. *)
let punctuation cursor current =
  let start = cursor.position in
  let at offset = byte cursor (start + offset) in
  let is offset character = at offset = Char.code character in
  let take kind length =
    cursor.position <- start + length;
    Some (Punctuation kind)
  in
  let followed_by options default =
    match List.find_opt (fun (character, _, _) -> is 1 character) options with
    | Some (_, kind, length) -> take kind length
    | None -> take default 1
  in
  match current with
  | '(' -> take (Open Paren) 1
  | ')' -> take (Close Paren) 1
  | '[' -> take (Open Square) 1
  | ']' -> take (Close Square) 1
  | '{' -> take (Open Curly) 1
  | '}' -> take (Close Curly) 1
  | ',' -> take Comma 1
  | '?' -> take Question 1
  | '~' -> take Tilde 1
  | ':' -> followed_by [ (':', Colon_colon, 2) ] Colon
  | '.' ->
      if is 1 '.' then if is 2 '=' then take Dot_dot_equal 3 else take Dot_dot 2 else take Dot 1
  | '-' ->
      if is 1 '-' then begin
        cursor.position <- start + 2;
        Some (Foreign Minus_minus)
      end
      else followed_by [ ('>', Arrow, 2); ('=', Minus_equal, 2) ] Minus
  | '+' ->
      if is 1 '+' then begin
        cursor.position <- start + 2;
        Some (Foreign Plus_plus)
      end
      else followed_by [ ('=', Plus_equal, 2) ] Plus
  | '*' -> followed_by [ ('=', Star_equal, 2) ] Star
  | '/' -> followed_by [ ('=', Slash_equal, 2) ] Slash
  | '%' -> followed_by [ ('=', Percent_equal, 2) ] Percent
  | '^' -> followed_by [ ('=', Caret_equal, 2) ] Caret
  | '&' -> followed_by [ ('&', And_and, 2); ('=', Ampersand_equal, 2) ] Ampersand
  | '|' -> followed_by [ ('|', Or_or, 2); ('=', Bar_equal, 2) ] Bar
  (* JavaScript's `===` and `!==`, as a whole: a longer run of `=` is not
     that habit, and lexes as `==`s for the parser to report. *)
  | ('=' | '!') when is 1 '=' && is 2 '=' && not (is 3 '=') ->
      let written, replacement, kind =
        if current = '=' then ("===", "==", Equal_equal) else ("!==", "!=", Not_equal)
      in
      report cursor ~code:Strict_equality
        ~fixes:
          [
            Diagnostic.fix
              ("Write `" ^ replacement ^ "`")
              [ Diagnostic.replace (span start (start + 3)) replacement ];
          ]
        (span start (start + 3))
        (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
           replacement);
      take kind 3
  | '=' when is 1 '=' && is 2 '>' -> take Implies 3
  | '=' -> followed_by [ ('=', Equal_equal, 2); ('>', Fat_arrow, 2) ] Equal
  | '!' -> followed_by [ ('=', Not_equal, 2) ] Bang
  | '<' ->
      if is 1 '<' then if is 2 '=' then take Shift_left_equal 3 else take Shift_left 2
      else followed_by [ ('=', Less_equal, 2) ] Less
  | '>' ->
      if is 1 '>' then if is 2 '=' then take Shift_right_equal 3 else take Shift_right 2
      else followed_by [ ('=', Greater_equal, 2) ] Greater
  | _ -> None

(* Checks a name, once per spelling in the file. *)
let checked_name cursor name =
  match Hashtbl.find_opt cursor.names name with
  | Some checked -> checked
  | None ->
      let checked = Names.check name in
      Hashtbl.add cursor.names name checked;
      checked

let number cursor =
  let start = cursor.position in
  let stop = Numbers.scan_end cursor.text start in
  cursor.position <- stop;
  let checked = Numbers.check (String.sub cursor.text start (stop - start)) in
  (match checked.problem with
  | Some problem ->
      report cursor ~code:problem.code
        ~fixes:
          (List.map
             (fun (title, replacement) ->
               Diagnostic.fix title [ Diagnostic.replace (span start stop) replacement ])
             checked.fixes)
        (span (start + problem.start) (start + problem.stop))
        problem.message
  | None -> ());
  checked.value

let rec scan cursor ~inline ~nesting =
  let start = cursor.position in
  let current = byte cursor start in
  let next = byte cursor (start + 1) in
  let again () = scan cursor ~inline ~nesting in
  let reject ?code length message =
    Trivia.reject ?code cursor ~length message;
    again ()
  in
  let token kind = Token { kind; start; ending = Closed } in
  let forbidden () =
    Source_text.forbidden_run cursor ~context:Code;
    cursor.line_is_blank <- false;
    again ()
  in
  if current < 0 then End
  else if is_space current then begin
    cursor.position <- start + 1;
    again ()
  end
  else if is_line_break current then Line_end
  else if is_ascii_letter current || current = Char.code '_' then name cursor ~nesting
  else if is_digit current then token (number cursor)
  else if current >= 0x80 then begin
    let packed = decode cursor start in
    if packed < 0 then begin
      Source_text.invalid_run cursor;
      again ()
    end
    else
      let value = Unicode.decoded_code_point packed in
      if Unicode.is_forbidden value then forbidden ()
      else if Unicode.is_xid_start value then name cursor ~nesting
      else
        reject (Unicode.decoded_length packed)
          (Printf.sprintf "%s is not used in Truss." (show_character cursor start))
  end
  else if current < 0x20 || current = 0x7F then forbidden ()
  else
    match Char.chr current with
    | '"' -> string cursor ~tag:None ~nesting ~start
    | '$' when Trivia.opens_raw_string cursor start -> string cursor ~tag:None ~nesting ~start
    | '$' ->
        reject (run_length cursor start dollar)
          "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s before a \
           raw string's `\"\"\"` choose how it interpolates."
    | '\'' -> (
        match Trivia.character_literal_end cursor start with
        | Some stop -> token (Strings.character_literal cursor ~stop)
        | None -> reject 1 "`'` is not used in Truss. Strings are written with `\"`.")
    | '/' when next = Char.code '/' || next = Char.code '*' ->
        if inline then reject ~code:Comment 2 Trivia.comment_message
        else begin
          if next = Char.code '/' then Trivia.line_comment cursor else Trivia.block_comment cursor;
          again ()
        end
    | '#' ->
        if inline then reject ~code:Comment 1 Trivia.comment_message
        else begin
          Trivia.line_comment cursor;
          again ()
        end
    | ';' ->
        if inline then reject ~code:Semicolon 1 "Truss has no `;`."
        else begin
          Trivia.semicolon cursor;
          again ()
        end
    | '`' -> reject 1 "The backtick is not used in Truss."
    | character -> (
        match punctuation cursor character with
        | Some kind -> token kind
        | None -> reject 1 (Printf.sprintf "`%c` is not used in Truss." character))

and string cursor ~tag ~nesting ~start =
  let kind, ending = Strings.scan_string cursor ~scan ~tag ~nesting in
  Token { kind; start; ending }

and name cursor ~nesting =
  let start = cursor.position in
  let rec loop () =
    let current = byte cursor cursor.position in
    if current >= 0 && current < 0x80 then
      begin if is_ascii_name_byte current then begin
        cursor.position <- cursor.position + 1;
        loop ()
      end
      end
    else
      let packed = decode cursor cursor.position in
      if packed >= 0 && Unicode.is_xid_continue (Unicode.decoded_code_point packed) then begin
        cursor.position <- cursor.position + Unicode.decoded_length packed;
        loop ()
      end
  in
  loop ();
  let stop = cursor.position in
  let spelling = String.sub cursor.text start (stop - start) in
  let kind =
    if spelling = "_" then Underscore
    else
      match Token.word spelling with
      | Some kind -> kind
      | None ->
          let checked = checked_name cursor spelling in
          (match checked.problem with
          | Some (code, message) ->
              let fixes =
                match checked.fix with
                | Some fixed ->
                    [
                      Diagnostic.fix
                        ("Write `" ^ fixed ^ "`")
                        [ Diagnostic.replace (span start stop) fixed ];
                    ]
                | None -> []
              in
              report cursor ~code ~fixes (span start stop) message
          | None -> ());
          if checked.kind = Names.Upper then Upper checked.name else Lower checked.name
  in
  (* An UpperCamelCase name touching a string is the string's tag. *)
  match kind with
  | Upper tag
    when byte cursor stop = quote
         || (byte cursor stop = dollar && Trivia.opens_raw_string cursor stop) ->
      string cursor ~tag:(Some (tag, span start stop)) ~nesting ~start
  | kind -> Token { kind; start; ending = Closed }

(* The next raw token of the file. Line breaks between tokens are trivia
   here. *)
let rec next cursor =
  match scan cursor ~inline:false ~nesting:0 with
  | Line_end ->
      Source_text.note_line_break cursor (Source_text.consume_line_break cursor);
      next cursor
  | End ->
      Layout.End
        {
          position = cursor.length;
          first_line_break = cursor.first_line_break;
          blank_line = cursor.blank_line;
          ends_unterminated = cursor.unterminated_at_end;
        }
  | Token { kind; start; ending } ->
      let first_line_break = cursor.first_line_break and blank_line = cursor.blank_line in
      cursor.first_line_break <- None;
      cursor.blank_line <- false;
      cursor.line_is_blank <- false;
      Layout.Next
        {
          kind;
          span = span start cursor.position;
          first_line_break;
          blank_line;
          unterminated_string = ending = Unterminated;
        }

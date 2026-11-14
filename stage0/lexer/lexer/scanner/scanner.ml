(* Bytes to raw tokens.

   The scanner is an index moving over the file's bytes. ASCII bytes are
   handled directly, and a byte of 0x80 or above starts a UTF-8 sequence,
   which is decoded strictly.

   [scan] looks at each position once and decides there whether it holds
   trivia, which it skips, or the start of a token, which it reads. It reads
   Truss; the forms of other languages are the modules of [Habits], which it
   asks first where one can start. *)

open Token
open Cursor

type t = Cursor.t

let create = Cursor.create ~foreign_escape:Habits.Escapes.scan

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
  | '-' -> followed_by [ ('>', Arrow, 2); ('=', Minus_equal, 2) ] Minus
  | '+' -> followed_by [ ('=', Plus_equal, 2) ] Plus
  | '*' -> followed_by [ ('=', Star_equal, 2) ] Star
  | '/' -> followed_by [ ('=', Slash_equal, 2) ] Slash
  | '%' -> followed_by [ ('=', Percent_equal, 2) ] Percent
  | '^' -> followed_by [ ('=', Caret_equal, 2) ] Caret
  | '&' -> followed_by [ ('&', And_and, 2); ('=', Ampersand_equal, 2) ] Ampersand
  | '|' -> followed_by [ ('|', Or_or, 2); ('=', Bar_equal, 2) ] Bar
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

let ends_operand : Token.kind -> bool = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Close _ | Question) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable) -> true
  | _ -> false

let follows_operand cursor =
  match cursor.previous with Some kind -> ends_operand kind | None -> false

let begins_operand : Token.kind -> bool = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Open (Paren | Square)) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable) -> true
  | _ -> false

let is_word : Token.kind -> bool = function
  | Upper _ | Lower _ | Underscore | Keyword _ | Reserved _ -> true
  | _ -> false

(* [word_follows index]: whether a word follows [index] on its line. *)
let number cursor ~word_follows =
  let start = cursor.position in
  let stop = Habits.Number_forms.scan_end cursor.text start in
  cursor.position <- stop;
  let checked = Habits.Number_forms.check (String.sub cursor.text start (stop - start)) in
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
  Habits.Number_forms.after_integer cursor ~start ~stop ~word_follows checked

let rec scan cursor ~inline ~nesting =
  let item = scan_item cursor ~inline ~nesting in
  (match item with Token { kind; _ } -> cursor.previous <- Some kind | Line_end | End -> ());
  item

and scan_item cursor ~inline ~nesting =
  let start = cursor.position in
  let current = byte cursor start in
  let next = byte cursor (start + 1) in
  let again () = scan_item cursor ~inline ~nesting in
  let next_kind index =
    match scan_item (peek cursor index) ~inline ~nesting with
    | Token { kind; _ } -> Some kind
    | Line_end | End -> None
  in
  let reject ?code length message =
    Source_text.reject ?code cursor ~length message;
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
  else if is_digit current then
    token
      (number cursor ~word_follows:(fun index ->
           match next_kind index with Some kind -> is_word kind | None -> false))
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
        let length = Unicode.decoded_length packed in
        let unused () =
          reject length (Printf.sprintf "%s is not used in Truss." (show_character cursor start))
        in
        match Habits.Confusables.scan cursor ~value ~length with
        | Some (Lexed kind) -> token kind
        | Some Spaced -> again ()
        | None -> unused ()
  end
  else if current < 0x20 || current = 0x7F then forbidden ()
  else if Habits.Comments.scan cursor ~inline then again ()
  else
    let operand_follows index =
      match next_kind index with Some kind -> begins_operand kind | None -> false
    in
    match
      Habits.Operators.scan cursor ~follows_operand:(follows_operand cursor) ~operand_follows
    with
    | Some (Lexed kind) -> token kind
    | Some Skipped -> again ()
    | None -> (
        match
          if current = dollar && Strings.opens_raw_string cursor start then None
          else Habits.String_forms.scan cursor ~scan ~nesting
        with
        | Some (Lexed (kind, ending)) -> Token { kind; start; ending }
        | Some Skipped -> again ()
        | None -> (
            match Char.chr current with
            | '"' -> string cursor ~tag:None ~nesting ~start
            | '$' when Strings.opens_raw_string cursor start ->
                string cursor ~tag:None ~nesting ~start
            | '$' ->
                reject (run_length cursor start dollar)
                  "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s \
                   before a raw string's `\"\"\"` choose how it interpolates."
            | '.' when is_digit next && not (follows_operand cursor) -> (
                match Habits.Number_forms.leading_dot cursor with
                | Some kind -> token kind
                | None -> (
                    match punctuation cursor '.' with Some kind -> token kind | None -> again ()))
            | character -> (
                match punctuation cursor character with
                | Some kind -> token kind
                | None -> reject 1 (Printf.sprintf "`%c` is not used in Truss." character))))

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
         || (byte cursor stop = dollar && Strings.opens_raw_string cursor stop) ->
      string cursor ~tag:(Some (tag, span start stop)) ~nesting ~start
  | kind -> (
      match Habits.String_forms.after_name cursor ~scan ~nesting ~start kind with
      | Some (kind, ending) -> Token { kind; start; ending }
      | None -> Token { kind; start; ending = Closed })

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

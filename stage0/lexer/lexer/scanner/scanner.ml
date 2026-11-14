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
  (* An operator of another language that one Truss operator replaces. *)
  let foreign_operator ~written ~replacement =
    let stop = start + String.length written in
    report cursor ~code:Foreign_operator
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ replace_code cursor (span start stop) replacement ];
        ]
      (span start stop)
      (Printf.sprintf "Truss has no `%s`; write `%s`." written replacement)
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
  | ':' when is 1 '=' ->
      cursor.position <- start + 2;
      Some (Foreign Colon_equal)
  | ':' -> followed_by [ (':', Colon_colon, 2) ] Colon
  (* Swift's half-open range, `..<`, is Truss's `..`. *)
  | '.' when is 1 '.' && is 2 '<' ->
      foreign_operator ~written:"..<" ~replacement:"..";
      take Dot_dot 3
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
  | '*' when is 1 '*' ->
      cursor.position <- start + 2;
      Some (Foreign Star_star)
  | '*' -> followed_by [ ('=', Star_equal, 2) ] Star
  | '/' -> followed_by [ ('=', Slash_equal, 2) ] Slash
  | '%' -> followed_by [ ('=', Percent_equal, 2) ] Percent
  | '^' -> followed_by [ ('=', Caret_equal, 2) ] Caret
  | '&' -> followed_by [ ('&', And_and, 2); ('=', Ampersand_equal, 2) ] Ampersand
  | '|' when is 1 '>' ->
      cursor.position <- start + 2;
      Some (Foreign Pipe_greater)
  | '|' -> followed_by [ ('|', Or_or, 2); ('=', Bar_equal, 2) ] Bar
  | ('=' | '!') when is 1 '=' && is 2 '=' && not (is 3 '=') ->
      let written, replacement, kind =
        if current = '=' then ("===", "==", Equal_equal) else ("!==", "!=", Not_equal)
      in
      report cursor ~code:Strict_equality
        ~fixes:
          [
            Diagnostic.fix
              ("Write `" ^ replacement ^ "`")
              [ replace_code cursor (span start (start + 3)) replacement ];
          ]
        (span start (start + 3))
        (Printf.sprintf "Truss has no `%s`. `%s` already compares values of the same type." written
           replacement);
      take kind 3
  | '=' when is 1 '=' && is 2 '>' -> take Implies 3
  | '=' -> followed_by [ ('=', Equal_equal, 2); ('>', Fat_arrow, 2) ] Equal
  | '!' -> followed_by [ ('=', Not_equal, 2) ] Bang
  (* The inequality of SQL and Pascal, `<>`, is Truss's `!=`. *)
  | '<' when is 1 '>' ->
      foreign_operator ~written:"<>" ~replacement:"!=";
      take Not_equal 2
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

(* Whether a name, or a keyword that a confusable character such as `∀` spells, starts
   at [index]: after `1.`, it makes the `.` a member access. *)
let starts_name cursor index =
  let current = byte cursor index in
  if current < 0x80 then is_ascii_name_byte current
  else
    let packed = decode cursor index in
    packed >= 0
    &&
    let value = Unicode.decoded_code_point packed in
    Unicode.is_xid_start value
    ||
    match Confusables.find value with
    | Some (Spelled spelling) -> Token.word spelling <> None
    | _ -> false

(* The first offset at or after [index] that holds no space, line break, or
   character that its fix replaces with a space, such as U+00A0. *)
let rec skip_blank_and_confusable_spaces cursor index =
  let position = Source_text.skip_blank cursor index in
  let packed = if byte cursor position >= 0x80 then decode cursor position else -1 in
  if packed >= 0 && Confusables.find (Unicode.decoded_code_point packed) = Some Confusables.Space
  then skip_blank_and_confusable_spaces cursor (position + Unicode.decoded_length packed)
  else position

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
               Diagnostic.fix title [ replace_code cursor (span start stop) replacement ])
             checked.fixes)
        (span (start + problem.start) (start + problem.stop))
        problem.message
  | None -> ());
  match checked with
  (* `1.`, with nothing after the `.` that a member access could continue
     with: a float with no digit after its `.`. *)
  | { value = Integer _; problem = None; _ }
    when byte cursor stop = Char.code '.'
         && (not (Numbers.is_radix_prefix cursor.text start))
         &&
         let after = skip_blank_and_confusable_spaces cursor (stop + 1) in
         not (starts_name cursor after || byte cursor after = Char.code '.') -> (
      let written = String.sub cursor.text start (stop + 1 - start) in
      match Numbers.float_with_zero (written ^ "0") with
      | Some value ->
          cursor.position <- stop + 1;
          report cursor ~code:Number_missing_digits
            ~fixes:
              [
                Diagnostic.fix
                  (Printf.sprintf "Write `%s0`" written)
                  [ replace_code cursor (Source.zero_width (stop + 1)) "0" ];
              ]
            (span stop (stop + 1))
            (Printf.sprintf "A float has a digit after its `.`: `%s0`." written);
          value
      | None -> checked.value)
  | _ -> checked.value

(* `.5`, where no operand comes before the `.`: a float with no digit before
   its `.`. Its fix writes the `0`, and corrects the literal's other
   problems with it, as `.5f` to `0.5`. [None] when the text with the `0`
   written is not a float, or has a problem with no fix. *)
let leading_dot_float cursor =
  let start = cursor.position in
  let stop = Numbers.scan_end cursor.text (start + 1) in
  let written = String.sub cursor.text start (stop - start) in
  let checked = Numbers.check ("0" ^ written) in
  let fixed =
    match (checked.value, checked.problem, checked.fixes) with
    | Float _, None, _ -> Some ("0" ^ written, replace_code cursor (Source.zero_width start) "0")
    | Float _, Some _, (_, fixed) :: _ -> Some (fixed, replace_code cursor (span start stop) fixed)
    | _ -> None
  in
  match fixed with
  | Some (fixed, edit) ->
      cursor.position <- stop;
      report cursor ~code:Number_missing_digits
        ~fixes:[ Diagnostic.fix (Printf.sprintf "Write `%s`" fixed) [ edit ] ]
        (span start (start + 1))
        (Printf.sprintf "A float has a digit before its `.`: `%s`." fixed);
      Some checked.value
  | None -> None

(* `...`, which is three things in other languages. Between two operands
   it is the inclusive range of Ruby and Swift, and lexes as `..=`. With an
   operand on neither side it is a placeholder for code not written yet, as
   in Python, and lexes as `todo`. Before an operand only, it is the spread
   or rest operator, which Truss does not have, and lexes as nothing. *)
let ellipsis cursor =
  let start = cursor.position in
  let stop = start + 3 in
  let after = Trivia.after_operand cursor start and before = Trivia.before_operand cursor stop in
  cursor.position <- stop;
  cursor.line_is_blank <- false;
  let replaced replacement message kind =
    report cursor ~code:Foreign_operator
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ replace_code cursor (span start stop) replacement ];
        ]
      (span start stop) message;
    Some kind
  in
  if after && before then
    replaced "..=" "Truss has no `...`; a range that includes its end is written `..=`."
      (Punctuation Dot_dot_equal)
  else if (not after) && not before then
    replaced "todo" "Truss has no `...`; code that is not written yet is `todo`." (Keyword Todo)
  else begin
    report cursor ~code:Foreign_operator (span start stop)
      "Truss has no `...`: it has no spread or rest operator, and a function takes a list where it \
       takes any number of values.";
    None
  end

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
        let length = Unicode.decoded_length packed in
        let unused () =
          reject length (Printf.sprintf "%s is not used in Truss." (show_character cursor start))
        in
        (* A character that looks like ASCII punctuation is reported, and
           lexes as the token that its fix writes: `p∀x` as `p forall x`,
           and `–>` as `- >`. *)
        let confusable ~replacement ~name =
          report cursor ~code:Confusable_character
            ~fixes:
              [
                Diagnostic.fix
                  ("Write `" ^ replacement ^ "`")
                  [ replace_code cursor (span start (start + length)) replacement ];
              ]
            (span start (start + length))
            (Printf.sprintf "%s is not %s. Truss is written with ASCII punctuation."
               (show_character cursor start) name);
          cursor.position <- start + length;
          cursor.line_is_blank <- false
        in
        match Confusables.find value with
        | Some Space ->
            confusable ~replacement:" " ~name:"the space character";
            again ()
        | Some (Spelled spelling) -> (
            match Confusables.token spelling with
            | Some kind ->
                confusable ~replacement:spelling ~name:("`" ^ spelling ^ "`");
                token kind
            | None -> unused ())
        | Some (Opening_quote closing) -> (
            match Strings.curly_quoted_string cursor ~opening_length:length ~closing with
            | Some kind -> token kind
            | None -> unused ())
        | None -> unused ()
  end
  else if current < 0x20 || current = 0x7F then forbidden ()
  else
    match Char.chr current with
    | '"' -> string cursor ~tag:None ~nesting ~start
    | '$' when Trivia.opens_raw_string cursor start -> string cursor ~tag:None ~nesting ~start
    (* C#'s interpolated string, `$"..."`. *)
    | '$' when next = quote ->
        cursor.position <- start + 1;
        let kind, ending = Strings.prefixed_string cursor ~scan ~prefix:"$" ~start ~nesting in
        Token { kind; start; ending }
    | '$' ->
        reject (run_length cursor start dollar)
          "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s before a \
           raw string's `\"\"\"` choose how it interpolates."
    | '\'' -> (
        match Trivia.character_literal_end cursor start with
        | Some stop ->
            token (Strings.character_literal cursor ~tag:"Character" ~literal_start:start ~stop)
        | None -> (
            let touches_name index =
              let neighbor = byte cursor index in
              is_ascii_name_byte neighbor || neighbor >= 0x80
            in
            match Strings.closing_delimiter cursor ~start ~delimiter:current with
            (* A string of Python or JavaScript, `'abc'`. A quote that
               touches a name on its outer side is not one: it is an
               apostrophe, or it opens a lifetime of Rust. *)
            | Some close
              when (not (start > 0 && touches_name (start - 1))) && not (touches_name (close + 1))
              ->
                let kind, ending = Strings.quoted_string cursor ~scan ~nesting ~delimiter:current in
                Token { kind; start; ending }
            | _
              when (is_ascii_letter next || next = Char.code '_')
                   && not (start > 0 && touches_name (start - 1)) ->
                let rec name_end position =
                  if is_ascii_name_byte (byte cursor position) then name_end (position + 1)
                  else position
                in
                reject ~code:Lifetime
                  (name_end (start + 1) - start)
                  "Truss has no lifetimes. How long a view lasts is checked without annotations."
            | _ -> reject 1 "`'` is not used in Truss. Strings are written with `\"`."))
    | '/' when next = Char.code '/' || next = Char.code '*' ->
        if inline then reject ~code:Comment 2 Trivia.comment_message
        else begin
          if next = Char.code '/' then Trivia.line_comment cursor else Trivia.block_comment cursor;
          again ()
        end
    | '#'
      when next = Char.code '[' || (next = Char.code '!' && byte cursor (start + 2) = Char.code '[')
      ->
        if inline then reject ~code:Attribute 1 "Truss has no attributes."
        else begin
          Trivia.attribute cursor;
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
    | '.' when is_digit next && not (Trivia.after_operand cursor start) -> (
        match leading_dot_float cursor with
        | Some kind -> token kind
        | None -> ( match punctuation cursor '.' with Some kind -> token kind | None -> again ()))
    | '`' -> (
        (* A template literal of JavaScript that closes on its line. *)
        match Strings.closing_delimiter cursor ~start ~delimiter:current with
        | Some _ ->
            let kind, ending = Strings.quoted_string cursor ~scan ~nesting ~delimiter:current in
            Token { kind; start; ending }
        | None -> reject 1 "The backtick is not used in Truss.")
    (* C#'s verbatim string, `@"..."`. *)
    | '@' when next = quote ->
        cursor.position <- start + 1;
        let kind, ending = Strings.prefixed_string cursor ~scan ~prefix:"@" ~start ~nesting in
        Token { kind; start; ending }
    | '.' when next = Char.code '.' && byte cursor (start + 2) = Char.code '.' -> (
        match ellipsis cursor with Some kind -> token kind | None -> again ())
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
  (* A prefix from another language before an ordinary or an empty string. *)
  | Lower "r" when byte cursor stop = Char.code '#' -> (
      match Strings.hash_raw_string cursor ~start with
      | Some kind -> Token { kind; start; ending = Closed }
      | None -> Token { kind; start; ending = Closed })
  | Lower (("f" | "r" | "b") as prefix)
    when byte cursor stop = quote && (prefix <> "b" || run_length cursor stop quote <= 2) ->
      let kind, ending = Strings.prefixed_string cursor ~scan ~prefix ~start ~nesting in
      Token { kind; start; ending }
  | Lower "b" when byte cursor stop = Char.code '\'' -> (
      match Trivia.character_literal_end cursor stop ~after_prefix:true with
      | Some literal_stop ->
          let kind =
            Strings.character_literal cursor ~tag:"UInt8" ~literal_start:start ~stop:literal_stop
          in
          Token { kind; start; ending = Closed }
      | None -> Token { kind; start; ending = Closed })
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

type t = Cursor.t

let create = Cursor.create ~scan_foreign_escape:Habits.Escapes.scan

let lex_punctuation (cursor : Cursor.t) current =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let take kind length =
    cursor.position <- start + length;
    Some (Token.Punctuation kind)
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

let check_name (cursor : Cursor.t) name =
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

let follows_operand (cursor : Cursor.t) =
  match cursor.previous with Some token -> ends_operand token.kind | None -> false

let begins_operand : Token.kind -> bool = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Open (Paren | Square)) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable) -> true
  | _ -> false

let is_word : Token.kind -> bool = function
  | Upper _ | Lower _ | Underscore | Keyword _ | Reserved _ -> true
  | _ -> false

let make_token cursor ~inline ~start ?(ending = Cursor.Closed) kind =
  Habits.Comments.report_semicolons cursor
    ~line_break:(match kind with Token.Punctuation (Close Curly) -> false | _ -> true);
  let first_line_break = if inline then None else cursor.first_line_break in
  let blank_line = (not inline) && cursor.blank_line in
  if not inline then begin
    cursor.first_line_break <- None;
    cursor.blank_line <- false;
    cursor.line_is_blank <- false
  end;
  { Cursor.kind; start; stop = cursor.position; ending; first_line_break; blank_line }

let hold (cursor : Cursor.t) items = cursor.held <- items @ cursor.held

let attach_trivia (skipped : Cursor.token) (next : Cursor.token) =
  {
    next with
    first_line_break =
      (match skipped.first_line_break with
      | Some _ as line_break -> line_break
      | None -> next.first_line_break);
    blank_line = skipped.blank_line || next.blank_line;
  }

let restore_trivia (cursor : Cursor.t) (skipped : Cursor.token) =
  (match skipped.first_line_break with
  | Some _ as line_break -> cursor.first_line_break <- line_break
  | None -> ());
  cursor.blank_line <- skipped.blank_line || cursor.blank_line

let rec scan (cursor : Cursor.t) ~inline ~nesting =
  let item =
    match cursor.held with
    | item :: rest ->
        cursor.held <- rest;
        item
    | [] -> scan_item cursor ~inline ~nesting
  in
  (match item with Token token -> cursor.previous <- Some token | Line_end | End -> ());
  item

and scan_after (cursor : Cursor.t) ~inline ~nesting previous =
  cursor.previous <- previous;
  scan_item cursor ~inline ~nesting

and scan_item cursor ~inline ~nesting =
  let start = cursor.position in
  let again () = scan_item cursor ~inline ~nesting in
  let reject length message =
    Source_text.reject cursor ~length message;
    again ()
  in
  let token ?ending kind = Cursor.Token (make_token cursor ~inline ~start ?ending kind) in
  let forbidden () =
    Source_text.report_forbidden_run cursor ~context:Code;
    cursor.line_is_blank <- false;
    again ()
  in
  let no_token item =
    Habits.Comments.report_semicolons cursor ~line_break:false;
    item
  in
  if Cursor.is_at_end cursor start then no_token Cursor.End
  else
    let current = Cursor.lookup_char cursor start in
    if Cursor.is_space current then begin
      cursor.position <- start + 1;
      again ()
    end
    else if Cursor.is_line_break current then no_token Cursor.Line_end
    else if Cursor.is_ascii_letter current || current = '_' then lex_name cursor ~inline ~nesting
    else if Cursor.is_digit current then lex_number cursor ~inline ~nesting
    else if not (Cursor.is_ascii current) then begin
      let decoded = Cursor.decode cursor start in
      if not (Uchar.utf_decode_is_valid decoded) then begin
        Source_text.report_invalid_run cursor;
        again ()
      end
      else
        let scalar_value = Uchar.utf_decode_uchar decoded in
        if Unicode.is_forbidden scalar_value then forbidden ()
        else if Unicode.is_xid_start scalar_value then lex_name cursor ~inline ~nesting
        else
          let length = Uchar.utf_decode_length decoded in
          let unused () =
            reject length
              (Printf.sprintf "%s is not used in Truss." (Cursor.show_character cursor start))
          in
          match Habits.Confusables.scan cursor ~scalar_value ~length with
          | Some (Lexed kind) -> token kind
          | Some Spaced -> again ()
          | None -> unused ()
    end
    else if current < ' ' || current = '\x7F' then forbidden ()
    else if Habits.Comments.scan cursor ~inline then again ()
    else
      match Habits.Operators.scan cursor with
      | Some (Lexed kind) -> token kind
      | Some Ellipsis -> lex_ellipsis cursor ~inline ~nesting ~start
      | None -> (
          match
            if current = '$' && Strings.opens_raw_string cursor start then None
            else Habits.String_forms.scan cursor ~scan ~nesting
          with
          | Some (Lexed (kind, ending)) -> token ~ending kind
          | Some Skipped -> again ()
          | None -> (
              match current with
              | '"' -> lex_string cursor ~tag:None ~inline ~nesting ~start
              | '$' when Strings.opens_raw_string cursor start ->
                  lex_string cursor ~tag:None ~inline ~nesting ~start
              | '$' ->
                  reject
                    (Cursor.run_length cursor start '$')
                    "`$` is used only in strings: `${...}` inside a string interpolates, and `$`s \
                     before a raw string's `\"\"\"` choose how it interpolates."
              | '.'
                when Cursor.satisfies cursor (start + 1) Cursor.is_digit
                     && not (follows_operand cursor) -> (
                  match Habits.Number_forms.lex_leading_dot cursor with
                  | Some kind -> token kind
                  | None -> (
                      match lex_punctuation cursor '.' with
                      | Some kind -> token kind
                      | None -> again ()))
              | character -> (
                  match lex_punctuation cursor character with
                  | Some kind -> token kind
                  | None -> reject 1 (Printf.sprintf "`%c` is not used in Truss." character))))

and lex_number cursor ~inline ~nesting =
  let start = cursor.position in
  let stop = Habits.Number_forms.scan_end cursor.text start in
  cursor.position <- stop;
  let checked = Habits.Number_forms.check (String.sub cursor.text start (stop - start)) in
  (match checked.problem with
  | Some problem ->
      Cursor.report cursor ~code:problem.code
        ~fixes:
          (if Cursor.is_at cursor stop '.' then []
           else
             List.map
               (fun (title, replacement) ->
                 Diagnostic.fix title
                   [ Diagnostic.replace (Source.make_span start stop) replacement ])
               checked.fixes)
        (Source.make_span (start + problem.start) (start + problem.stop))
        problem.message
  | None -> ());
  let integer = make_token cursor ~inline ~start checked.value in
  match Habits.Number_forms.lex_trailing_point cursor ~start ~stop checked with
  | None -> Token integer
  | Some float -> (
      match scan_after cursor ~inline ~nesting (Some integer) with
      | Token ({ kind = Punctuation Dot; start = point; _ } as dot) when point = stop -> (
          let merged = { integer with kind = float; stop = dot.stop } in
          match scan_after cursor ~inline ~nesting (Some merged) with
          | Token { kind; _ } as following when is_word kind ->
              hold cursor [ Token dot; following ];
              Token integer
          | following ->
              Habits.Number_forms.report_trailing_point cursor ~start ~point;
              hold cursor [ following ];
              Token merged)
      | following ->
          hold cursor [ following ];
          Token integer)

and lex_ellipsis cursor ~inline ~nesting ~start =
  let follows_operand = follows_operand cursor in
  let raw = make_token cursor ~inline ~start (Punctuation Dot_dot_equal) in
  let following = scan_after cursor ~inline ~nesting None in
  let operand_follows =
    match following with Token token -> begins_operand token.kind | Line_end | End -> false
  in
  match Habits.Operators.lex_ellipsis cursor ~start ~follows_operand ~operand_follows with
  | Some kind ->
      hold cursor [ following ];
      Token { raw with kind }
  | None -> (
      match following with
      | Token token -> Token (attach_trivia raw token)
      | Line_end | End ->
          restore_trivia cursor raw;
          following)

and lex_string cursor ~tag ~inline ~nesting ~start =
  let kind, ending = Strings.scan_string cursor ~scan ~tag ~nesting in
  Token (make_token cursor ~inline ~start ~ending kind)

and lex_name cursor ~inline ~nesting =
  let start = cursor.position in
  let rec loop () =
    let position = cursor.position in
    if Cursor.is_at_end cursor position then ()
    else if Cursor.is_ascii (Cursor.lookup_char cursor position) then
      begin if Cursor.is_ascii_name_byte (Cursor.lookup_char cursor position) then begin
        cursor.position <- position + 1;
        loop ()
      end
      end
    else
      let decoded = Cursor.decode cursor position in
      if
        Uchar.utf_decode_is_valid decoded
        && Unicode.is_xid_continue (Uchar.utf_decode_uchar decoded)
      then begin
        cursor.position <- position + Uchar.utf_decode_length decoded;
        loop ()
      end
  in
  loop ();
  let stop = cursor.position in
  let spelling = String.sub cursor.text start (stop - start) in
  let kind =
    if spelling = "_" then Token.Underscore
    else
      match Token.find_word spelling with
      | Some kind -> kind
      | None ->
          let checked = check_name cursor spelling in
          (match checked.problem with
          | Some (code, message) ->
              let opens_literal =
                Cursor.is_at cursor stop '"' || Cursor.is_at cursor stop '\''
                || (Cursor.is_at cursor stop '$' && Strings.opens_raw_string cursor stop)
              in
              let fixes =
                match checked.fix with
                | Some fixed when (not opens_literal) || (fixed.[0] >= 'A' && fixed.[0] <= 'Z') ->
                    [
                      Diagnostic.fix
                        ("Write `" ^ fixed ^ "`")
                        [ Diagnostic.replace (Source.make_span start stop) fixed ];
                    ]
                | Some _ | None -> []
              in
              Cursor.report cursor ~code ~fixes (Source.make_span start stop) message
          | None -> ());
          if checked.kind = Names.Upper then Upper checked.name else Lower checked.name
  in
  match kind with
  | Upper tag
    when Cursor.is_at cursor stop '"'
         || (Cursor.is_at cursor stop '$' && Strings.opens_raw_string cursor stop) ->
      lex_string cursor ~tag:(Some (tag, Source.make_span start stop)) ~inline ~nesting ~start
  | kind -> (
      match Habits.String_forms.lex_after_name cursor ~scan ~nesting ~start kind with
      | Some (kind, ending) -> Token (make_token cursor ~inline ~start ~ending kind)
      | None -> Token (make_token cursor ~inline ~start kind))

let rec lex_next cursor =
  match scan cursor ~inline:false ~nesting:0 with
  | Line_end ->
      Source_text.note_line_break cursor (Source_text.consume_line_break cursor);
      lex_next cursor
  | End ->
      Layout.End
        {
          position = cursor.length;
          first_line_break = cursor.first_line_break;
          blank_line = cursor.blank_line;
          ends_unterminated = cursor.unterminated_at_end;
        }
  | Token token ->
      Layout.Next
        {
          kind = token.kind;
          span = Source.make_span token.start token.stop;
          first_line_break = token.first_line_break;
          blank_line = token.blank_line;
          unterminated_string = token.ending = Unterminated;
        }

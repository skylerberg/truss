(* Strings and characters written as other languages write them. *)

open Token
open Cursor

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

(* A character literal from another language, `'a'` or `'\n'`, whose
   opening quote is at the cursor and which ends at [stop]: reported, with a
   fix to the tagged string `Character"a"`, which is the token it becomes.
   [literal_start] is where the literal starts, which is before the quote
   for a byte literal, `b'a'`, whose [tag] is `UInt8`. *)
let character_literal cursor ~tag ~literal_start ~stop =
  let start = cursor.position in
  let content = String.sub cursor.text (start + 1) (stop - start - 2) in
  let as_ordinary = match content with "\"" -> "\\\"" | "\\'" -> "'" | other -> other in
  let value =
    match content with
    | "\\n" -> "\n"
    | "\\t" -> "\t"
    | "\\r" -> "\r"
    | "\\0" -> "\000"
    | "\\\\" -> "\\"
    | "\\\"" -> "\""
    | "\\'" -> "'"
    | escape when String.starts_with ~prefix:"\\u{" escape -> (
        match int_of_string_opt ("0x" ^ String.sub escape 3 (String.length escape - 4)) with
        | Some value when value <= 0x10FFFF && (value < 0xD800 || value > 0xDFFF) ->
            Unicode.of_code_points [ value ]
        | _ -> "")
    | other -> other
  in
  let replacement = tag ^ "\"" ^ as_ordinary ^ "\"" in
  report cursor ~code:Character_literal
    ~fixes:
      [
        Diagnostic.fix
          ("Write `" ^ replacement ^ "`")
          [ Diagnostic.replace (span literal_start stop) replacement ];
      ]
    (span literal_start stop)
    (Printf.sprintf "Truss has no %s literals. A single %s is a tagged string: `%s`."
       (if tag = "UInt8" then "byte" else "character")
       (if tag = "UInt8" then "byte" else "character")
       replacement);
  cursor.position <- stop;
  String
    {
      tag = Some (tag, Source.zero_width literal_start);
      form = Ordinary;
      first = { value; span = span (start + 1) (stop - 1) };
      rest = [||];
    }

(* The edits that turn the text of a Python f-string, between [start] and
   [stop], into a Truss string's: `{name}` becomes `${name}`, and `{{` and
   `}}` become `{` and `}`. [None] when a replacement field is not an
   expression alone, as `{value:.2f}` and `{}` are not, since no exact fix
   exists then. *)
let format_field_edits cursor ~start ~stop =
  let plain current =
    is_ascii_name_byte current || is_space current
    || List.mem (Char.chr current) [ '.'; ','; '('; ')'; '['; ']'; '+'; '-'; '*'; '/' ]
  in
  let rec field_end position =
    if position >= stop then None
    else if byte cursor position = Char.code '}' then Some position
    else if plain (byte cursor position) then field_end (position + 1)
    else None
  in
  let rec edits position reversed_edits =
    if position >= stop then Some (List.rev reversed_edits)
    else
      let current = Char.chr (byte cursor position) and next = byte cursor (position + 1) in
      match current with
      | '\\' -> edits (position + 2) reversed_edits
      | ('{' | '}') when next = Char.code current ->
          edits (position + 2)
            (Diagnostic.replace (span position (position + 2)) (String.make 1 current)
            :: reversed_edits)
      | '{' -> (
          match field_end (position + 1) with
          | Some close when skip_spaces cursor (position + 1) < close ->
              edits (close + 1)
                (Diagnostic.insert (Source.zero_width position) "$" :: reversed_edits)
          | _ -> None)
      | _ -> edits (position + 1) reversed_edits
  in
  edits start []

(* The meaning of a string prefix of another language. *)
type prefix_kind = Format | Raw_text | Bytes

let prefix_kind = function "f" | "$" -> Format | "r" | "@" -> Raw_text | _ -> Bytes

(* A string with a prefix from another language: `f"..."`, `r"..."`, and
   `b"..."` of Python and Rust, `$"..."` and `@"..."` of C#, and Python's
   `f"""..."""` and `r"""..."""`. The cursor is at the first quote after the
   prefix, which starts at [start]. The prefix is reported, and the token is
   the string that the fix writes: an ordinary string for a format string
   and a byte string, and a raw string for raw text and for three quotes. *)
let prefixed_string cursor ~scan ~prefix ~start ~nesting =
  let quote_start = cursor.position in
  let quotes = run_length cursor quote_start quote in
  let empty = quotes = 2 in
  let kind_of_prefix = prefix_kind prefix in
  let remove_prefix = Diagnostic.replace (span start quote_start) "" in
  let kind, ending =
    if kind_of_prefix = Raw_text && quotes = 1 then begin
      cursor.position <- quote_start + 1;
      Strings.scan_one_line_raw cursor ~scan ~tag:None
        ~form:(Raw { quotes = 3; dollars = 0; multi_line = false })
        ~nesting ~literal_start:start ~dollars:0 ~quotes:1
    end
    else Strings.scan_string cursor ~scan ~tag:None ~nesting
  in
  let delimiter = if empty then 1 else quotes in
  let text_start = quote_start + delimiter and text_stop = cursor.position - delimiter in
  let closed =
    ending = Closed && text_stop >= text_start && run_length cursor text_stop quote >= delimiter
  in
  let has_interpolations =
    match kind with String { rest; _ } -> Array.length rest > 0 | _ -> false
  in
  let contains character =
    let rec search position =
      position < text_stop && (byte cursor position = Char.code character || search (position + 1))
    in
    search text_start
  in
  let message, fixes =
    match kind_of_prefix with
    | Format ->
        ( Printf.sprintf
            "Truss has no `%s` strings. Every string interpolates with `${...}`, as in `\"Hello \
             ${name}\"`."
            prefix,
          if (not closed) || has_interpolations then []
          else if empty then [ Diagnostic.fix "Remove the prefix" [ remove_prefix ] ]
          else if quotes >= 3 && contains '\\' then
            (* Python applies escapes in `f"""..."""`, and a raw string has none. *)
            []
          else
            match format_field_edits cursor ~start:text_start ~stop:text_stop with
            | Some edits ->
                [
                  Diagnostic.fix
                    (if quotes = 1 then "Write an ordinary string" else "Write a raw string")
                    (remove_prefix :: edits);
                ]
            | None -> [] )
    | Raw_text ->
        ( Printf.sprintf
            "Truss has no `%s` strings. A raw string, which has no escapes, is written between \
             `\"\"\"`s, as in `\"\"\"\\d+\"\"\"`."
            prefix,
          if (not closed) || has_interpolations then []
          else if empty || quotes >= 3 then [ Diagnostic.fix "Remove the prefix" [ remove_prefix ] ]
          else if
            byte cursor (text_stop - 1) = Char.code '\\'
            (* C# writes a quote in `@"..."` as `""`. *)
            || byte cursor (text_stop + 1) = quote
          then []
          else
            [
              Diagnostic.fix "Write a raw string"
                [
                  Diagnostic.replace (span start text_start) "\"\"\"";
                  Diagnostic.replace (span text_stop (text_stop + 1)) "\"\"\"";
                ];
            ] )
    | Bytes ->
        ( "Truss has no byte strings. A string is UTF-8 text, and `text.bytes()` gives its bytes.",
          [] )
  in
  report cursor ~code:String_prefix ~fixes (span start quote_start) message;
  (kind, ending)

(* Rust's raw string with hashes, `r#"..."#`, which starts at the `r` at
   [start]; the cursor is at its first `#`. [None] when it is not closed on
   its line. The token is the raw string that the fix writes, whose
   delimiter is longer than every run of quotes in the text. *)
let hash_raw_string cursor ~start =
  let hashes = run_length cursor cursor.position (Char.code '#') in
  let text_start = cursor.position + hashes + 1 in
  let line_end = end_of_line cursor text_start in
  let rec close position =
    if position >= line_end then None
    else if
      byte cursor position = quote && run_length cursor (position + 1) (Char.code '#') >= hashes
    then Some position
    else close (position + 1)
  in
  if byte cursor (text_start - 1) <> quote then None
  else
    match close text_start with
    | None -> None
    | Some text_stop ->
        let value = String.sub cursor.text text_start (text_stop - text_start) in
        let rec longest_run position longest =
          if position >= text_stop then longest
          else
            let run = run_length cursor position quote in
            longest_run (position + max run 1) (max longest run)
        in
        let quotes = max 3 (longest_run text_start 0 + 1) in
        let delimiter = String.make quotes '"' in
        (* A one-line raw string cannot start or end with a quote, a `${`
           in it would interpolate, and a character that needs checking
           would be reported only after the fix. *)
        let exact =
          value <> ""
          && value.[0] <> '"'
          && value.[String.length value - 1] <> '"'
          && String.for_all (fun character -> character >= ' ' && character < '\x7F') value
          &&
          let rec no_interpolation index =
            index + 1 >= String.length value
            || (not (value.[index] = '$' && value.[index + 1] = '{'))
               && no_interpolation (index + 1)
          in
          no_interpolation 0
        in
        let stop = text_stop + 1 + hashes in
        report cursor ~code:String_prefix
          ~fixes:
            (if exact then
               [
                 Diagnostic.fix "Write a raw string"
                   [
                     Diagnostic.replace (span start text_start) delimiter;
                     Diagnostic.replace (span text_stop stop) delimiter;
                   ];
               ]
             else [])
          (span start text_start)
          "Truss has no `r#` strings. A raw string is written between `\"\"\"`s, or between more \
           quotes when its text has `\"\"\"` in it.";
        cursor.position <- stop;
        Some
          (String
             {
               tag = None;
               form = Raw { quotes; dollars = 0; multi_line = false };
               first = { value; span = span text_start text_stop };
               rest = [||];
             })

(* Where the string that [delimiter] opens at [start] closes on its line:
   the offset of the next [delimiter] that no `\` escapes. *)
let closing_delimiter cursor ~start ~delimiter =
  let rec search position =
    let current = byte cursor position in
    if is_end_of_line current then None
    else if current = Char.code '\\' then search (position + 2)
    else if current = delimiter then Some position
    else search (position + 1)
  in
  search (start + 1)

(* A string of another language between single quotes or backticks, which
   closes on its line: scanned as an ordinary string, and reported with a
   fix that writes it between `"`s and escapes each `"` in its text. The
   cursor is at the opening delimiter. *)
let quoted_string cursor ~scan ~nesting ~delimiter =
  let start = cursor.position in
  let kind, ending = Strings.scan_ordinary cursor ~closing:delimiter ~scan ~tag:None ~nesting in
  let stop = cursor.position in
  let inside_interpolation position =
    match kind with
    | String { rest; _ } ->
        Array.exists
          (fun ((inner : interpolation), _) ->
            inner.span.start <= position && position < inner.span.stop)
          rest
    | _ -> false
  in
  let rec quote_edits position reversed_edits =
    if position >= stop - 1 then List.rev reversed_edits
    else if byte cursor position = Char.code '\\' then quote_edits (position + 2) reversed_edits
    else if byte cursor position = quote && not (inside_interpolation position) then
      quote_edits (position + 1)
        (Diagnostic.insert (Source.zero_width position) "\\" :: reversed_edits)
    else quote_edits (position + 1) reversed_edits
  in
  let template = delimiter = Char.code '`' in
  report cursor ~code:String_delimiter
    ~fixes:
      (if ending = Closed then
         [
           Diagnostic.fix "Write the string between `\"`s"
             ((Diagnostic.replace (span start (start + 1)) "\"" :: quote_edits (start + 1) [])
             @ [ Diagnostic.replace (span (stop - 1) stop) "\"" ]);
         ]
       else [])
    (span start (start + 1))
    (if template then
       "Truss has no template literals. Every string is written between `\"`s and interpolates \
        with `${...}`."
     else "A string is written between `\"`s.");
  (kind, ending)

(* Text between curly quotes, as a word processor writes a string: “text”
   or ‘text’. The cursor is at the opening quote, [opening_length] bytes
   long, and [closing] is the closing quote's encoding. [None] when it does
   not close on its line. *)
let curly_quoted_string cursor ~opening_length ~closing =
  let start = cursor.position in
  let text_start = start + opening_length in
  let line_end = end_of_line cursor text_start in
  let rec close position =
    if position + String.length closing > line_end then None
    else if String.sub cursor.text position (String.length closing) = closing then Some position
    else close (position + 1)
  in
  match close text_start with
  | None -> None
  | Some text_stop ->
      let value = String.sub cursor.text text_start (text_stop - text_start) in
      let stop = text_stop + String.length closing in
      (* Text that an ordinary string would read differently has no exact fix. *)
      let exact =
        String.for_all
          (fun character ->
            character >= ' ' && character <> '"' && character <> '\\' && character <> '$')
          value
      in
      report cursor ~code:Confusable_character
        ~fixes:
          (if exact then
             [
               Diagnostic.fix "Write the string between `\"`s"
                 [
                   Diagnostic.replace (span start text_start) "\"";
                   Diagnostic.replace (span text_stop stop) "\"";
                 ];
             ]
           else [])
        (span start text_start)
        "A string is written between straight quotes, `\"`. This is a curly quote.";
      cursor.position <- stop;
      Some
        (String
           {
             tag = None;
             form = Ordinary;
             first = { value; span = span text_start text_stop };
             rest = [||];
           })

type scanned = Lexed of (Token.kind * Cursor.ending) | Skipped

(* A string or character of another language that starts at the cursor:
   `'a'`, `'abc'`, a backtick's template, C#'s `@"..."` and `$"..."`, or a
   lifetime or an apostrophe, rejected. [None] when none starts there. *)
let scan cursor ~scan ~nesting =
  let start = cursor.position in
  let current = byte cursor start and next = byte cursor (start + 1) in
  let token (kind, ending) = Some (Lexed (kind, ending)) in
  let rejected ?code length message =
    Source_text.reject ?code cursor ~length message;
    Some Skipped
  in
  let prefixed prefix =
    cursor.position <- start + 1;
    token (prefixed_string cursor ~scan ~prefix ~start ~nesting)
  in
  if current = Char.code '\'' then
    match character_literal_end cursor start with
    | Some stop ->
        token (character_literal cursor ~tag:"Character" ~literal_start:start ~stop, Closed)
    | None -> (
        (* Decoded, so that a symbol such as `→` is not a name character. *)
        let is_name_character position =
          let packed = decode cursor position in
          packed >= 0
          &&
          if byte cursor position < 0x80 then is_ascii_name_byte (byte cursor position)
          else Unicode.is_xid_continue (Unicode.decoded_code_point packed)
        in
        let touches_name_before index =
          let rec sequence_start position =
            if position > 0 && byte cursor position land 0xC0 = 0x80 then
              sequence_start (position - 1)
            else position
          in
          index > 0 && is_name_character (sequence_start (index - 1))
        in
        match closing_delimiter cursor ~start ~delimiter:current with
        (* A quote that touches a name on its outer side is an apostrophe,
           or opens a lifetime of Rust. *)
        | Some close when (not (touches_name_before start)) && not (is_name_character (close + 1))
          ->
            token (quoted_string cursor ~scan ~nesting ~delimiter:current)
        | _ when (is_ascii_letter next || next = Char.code '_') && not (touches_name_before start)
          ->
            let rec name_end position =
              if is_ascii_name_byte (byte cursor position) then name_end (position + 1)
              else position
            in
            rejected ~code:Lifetime
              (name_end (start + 1) - start)
              "Truss has no lifetimes. How long a view lasts is checked without annotations."
        | _ -> rejected 1 "`'` is not used in Truss. Strings are written with `\"`.")
  else if current = Char.code '`' then
    match closing_delimiter cursor ~start ~delimiter:current with
    | Some _ -> token (quoted_string cursor ~scan ~nesting ~delimiter:current)
    | None -> rejected 1 "The backtick is not used in Truss."
  else if current = Char.code '@' && next = quote then prefixed "@"
  else if current = dollar && next = quote then prefixed "$"
  else None

(* A string prefix of another language, the name from [start] to the
   cursor, before the string that follows it: `r#"..."#`, `f"..."`,
   `r"..."`, `b"..."`, and `b'a'`. [None] when no string follows. *)
let after_name cursor ~scan ~nesting ~start (name : Token.kind) =
  let stop = cursor.position in
  match name with
  | Lower "r" when byte cursor stop = Char.code '#' ->
      Option.map (fun kind -> (kind, Closed)) (hash_raw_string cursor ~start)
  | Lower (("f" | "r" | "b") as prefix)
    when byte cursor stop = quote && (prefix <> "b" || run_length cursor stop quote <= 2) ->
      Some (prefixed_string cursor ~scan ~prefix ~start ~nesting)
  | Lower "b" when byte cursor stop = Char.code '\'' ->
      Option.map
        (fun literal_stop ->
          (character_literal cursor ~tag:"UInt8" ~literal_start:start ~stop:literal_stop, Closed))
        (character_literal_end cursor stop ~after_prefix:true)
  | _ -> None

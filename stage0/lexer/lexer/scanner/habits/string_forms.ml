let touches_word_before (cursor : Cursor.t) index =
  match cursor.previous with
  | Some { stop; kind; _ } when stop = index -> (
      match kind with
      | Upper _ | Lower _ | Underscore | Keyword _ | Reserved _ -> true
      | Integer _ | Float _ -> Cursor.is_ascii_name_byte (Cursor.lookup_char cursor (index - 1))
      | _ -> false)
  | _ -> false

let quote_joins_before cursor index =
  touches_word_before cursor index || (index > 0 && Cursor.is_at cursor (index - 1) '"')

let is_name_character cursor position =
  (not (Cursor.is_at_end cursor position))
  &&
  let decoded = Cursor.decode cursor position in
  Uchar.utf_decode_is_valid decoded
  &&
  let current = Cursor.lookup_char cursor position in
  if Cursor.is_ascii current then Cursor.is_ascii_name_byte current
  else Unicode.is_xid_continue (Uchar.utf_decode_uchar decoded)

let find_character_literal_end ?(after_prefix = false) cursor start =
  if (not after_prefix) && touches_word_before cursor start then None
  else
    let content = start + 1 in
    let close =
      if Cursor.is_end_of_line cursor content || Cursor.is_at cursor content '\'' then None
      else if Cursor.is_at cursor content '\\' then
        if Cursor.is_at cursor (content + 1) 'u' && Cursor.is_at cursor (content + 2) '{' then
          match String.index_from_opt cursor.text (content + 3) '}' with
          | Some brace when brace - content <= 10 -> Some (brace + 1)
          | _ -> None
        else if
          Cursor.satisfies cursor (content + 1) (fun escaped ->
              List.mem escaped [ 'n'; 't'; 'r'; '0'; '\\'; '"'; '\'' ])
        then Some (content + 2)
        else None
      else
        let decoded = Cursor.decode cursor content in
        if
          (not (Uchar.utf_decode_is_valid decoded))
          || Unicode.is_forbidden (Uchar.utf_decode_uchar decoded)
        then None
        else Some (content + Uchar.utf_decode_length decoded)
    in
    match close with
    | Some close when Cursor.is_at cursor close '\'' && not (is_name_character cursor (close + 1))
      ->
        Some (close + 1)
    | _ -> None

let lex_character_literal (cursor : Cursor.t) ~tag ~literal_start ~stop =
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
        | Some value when Uchar.is_valid value ->
            let encoded = Buffer.create 4 in
            Buffer.add_utf_8_uchar encoded (Uchar.of_int value);
            Buffer.contents encoded
        | _ -> "")
    | other -> other
  in
  let replacement = tag ^ "\"" ^ as_ordinary ^ "\"" in
  Cursor.report cursor
    ~fixes:
      [
        {
          action = Write replacement;
          edits = [ { replaced = Source.make_span literal_start stop; code = Spelled replacement } ];
        };
      ]
    (Source.make_span literal_start stop)
    (Character_literal { is_byte = tag = "UInt8"; replacement });
  cursor.position <- stop;
  Token.String
    {
      tag = Some (tag, Source.make_zero_width literal_start);
      form = Ordinary;
      first = { value; span = Source.make_span (start + 1) (stop - 1) };
      rest = [||];
    }

let format_field_edits cursor ~start ~stop =
  let is_plain current =
    Cursor.is_ascii_name_byte current || Cursor.is_space current
    || List.mem current [ '.'; ','; '('; ')'; '['; ']'; '+'; '-'; '*'; '/' ]
  in
  let rec find_field_end position =
    if position >= stop then None
    else if Cursor.is_at cursor position '}' then Some position
    else if is_plain (Cursor.lookup_char cursor position) then find_field_end (position + 1)
    else None
  in
  let rec find_edits position reversed_edits =
    if position >= stop then Some (List.rev reversed_edits)
    else
      let current = Cursor.lookup_char cursor position in
      match current with
      | '\\' -> find_edits (position + 2) reversed_edits
      | ('{' | '}') when Cursor.is_at cursor (position + 1) current ->
          find_edits (position + 2)
            ({
               Syntax_catalog.Lexing.replaced = Source.make_span position (position + 2);
               code = Single_brace { is_opening = current = '{' };
             }
            :: reversed_edits)
      | '{' -> (
          match find_field_end (position + 1) with
          | Some close when Cursor.skip_spaces cursor (position + 1) < close ->
              find_edits (close + 1)
                ({ Syntax_catalog.Lexing.replaced = Source.make_zero_width position; code = Dollar }
                :: reversed_edits)
          | _ -> None)
      | _ -> find_edits (position + 1) reversed_edits
  in
  find_edits start []

type prefix_kind = Format | Raw_text | Bytes

let classify_prefix = function "f" | "$" -> Format | "r" | "@" -> Raw_text | _ -> Bytes

let lex_prefixed_string (cursor : Cursor.t) ~scan ~prefix ~start ~nesting =
  let quote_start = cursor.position in
  let quotes = Cursor.run_length cursor quote_start '"' in
  let empty = quotes = 2 in
  let kind_of_prefix = classify_prefix prefix in
  let remove_prefix : Syntax_catalog.Lexing.edit =
    { replaced = Source.make_span start quote_start; code = Removed }
  in
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
    ending = Closed && text_stop >= text_start
    && Cursor.run_length cursor text_stop '"' >= delimiter
  in
  let has_interpolations =
    match kind with String { rest; _ } -> Array.length rest > 0 | _ -> false
  in
  let closes_on_doubled_quote = Cursor.is_at cursor (text_stop - 1) '"' in
  let contains character =
    let rec search position =
      position < text_stop && (Cursor.is_at cursor position character || search (position + 1))
    in
    search text_start
  in
  let remove_prefix_fix : Syntax_catalog.Lexing.fix =
    { action = Remove_prefix; edits = [ remove_prefix ] }
  in
  let (problem : Syntax_catalog.Lexing.string_prefix), (fixes : Syntax_catalog.Lexing.fix list) =
    match kind_of_prefix with
    | Format ->
        ( Format_prefix prefix,
          if (not closed) || has_interpolations then []
          else if empty then [ remove_prefix_fix ]
          else if quotes >= 3 && contains '\\' then []
          else
            match format_field_edits cursor ~start:text_start ~stop:text_stop with
            | Some edits ->
                [
                  {
                    action = (if quotes = 1 then Write_ordinary_string else Write_raw_string);
                    edits = remove_prefix :: edits;
                  };
                ]
            | None -> [] )
    | Raw_text ->
        ( Raw_prefix prefix,
          if (not closed) || has_interpolations then []
          else if empty || quotes >= 3 then [ remove_prefix_fix ]
          else if Cursor.is_at cursor (text_stop - 1) '\\' || closes_on_doubled_quote then []
          else
            [
              {
                action = Write_raw_string;
                edits =
                  [
                    { replaced = Source.make_span start text_start; code = Quote_marks 3 };
                    { replaced = Source.make_span text_stop (text_stop + 1); code = Quote_marks 3 };
                  ];
              };
            ] )
    | Bytes -> (Byte_prefix, [])
  in
  Cursor.report cursor
    ~fixes:(if quote_joins_before cursor start then [] else fixes)
    (Source.make_span start quote_start)
    (String_prefix problem);
  (kind, ending)

let read_hash_raw_text (cursor : Cursor.t) ~text_start ~text_stop =
  let buffer = Buffer.create (text_stop - text_start) in
  cursor.position <- text_start;
  while cursor.position < text_stop do
    Source_text.copy_plain cursor buffer ~is_special:(fun character -> character = '"');
    if cursor.position < text_stop then Source_text.read_character cursor buffer ~context:Raw_string
  done;
  Buffer.contents buffer

let hash_raw_string cursor ~start =
  let hashes = Cursor.run_length cursor cursor.position '#' in
  let text_start = cursor.position + hashes + 1 in
  let line_end = Cursor.compute_end_of_line cursor text_start in
  let rec close position =
    if position >= line_end then None
    else if
      Cursor.is_at cursor position '"' && Cursor.run_length cursor (position + 1) '#' >= hashes
    then Some position
    else close (position + 1)
  in
  if not (Cursor.is_at cursor (text_start - 1) '"') then None
  else
    match close text_start with
    | None -> None
    | Some text_stop ->
        let written = String.sub cursor.text text_start (text_stop - text_start) in
        let rec measure_longest_run position longest =
          if position >= text_stop then longest
          else
            let run = Cursor.run_length cursor position '"' in
            measure_longest_run (position + max run 1) (max longest run)
        in
        let quotes = max 3 (measure_longest_run text_start 0 + 1) in
        let interpolates = String.includes ~affix:"${" written in
        let stop = text_stop + 1 + hashes in
        Cursor.report cursor
          ~fixes:
            (if
               interpolates || quote_joins_before cursor start
               || String.starts_with ~prefix:"\"" written
               || String.ends_with ~suffix:"\"" written
             then []
             else
               [
                 {
                   action = Write_raw_string;
                   edits =
                     [
                       { replaced = Source.make_span start text_start; code = Quote_marks quotes };
                       { replaced = Source.make_span text_stop stop; code = Quote_marks quotes };
                     ];
                 };
               ])
          (Source.make_span start text_start)
          Raw_hash_string;
        let value = read_hash_raw_text cursor ~text_start ~text_stop in
        cursor.position <- stop;
        Some
          (Token.String
             {
               tag = None;
               form = Raw { quotes; dollars = 0; multi_line = false };
               first = { value; span = Source.make_span text_start text_stop };
               rest = [||];
             })

let find_closing_delimiter cursor ~start ~delimiter =
  let rec search position =
    if Cursor.is_end_of_line cursor position then None
    else if Cursor.is_at cursor position '\\' then search (position + 2)
    else if Cursor.is_at cursor position delimiter then Some position
    else search (position + 1)
  in
  search (start + 1)

let lex_quoted_string (cursor : Cursor.t) ~scan ~nesting ~delimiter =
  let start = cursor.position in
  let kind, ending = Strings.scan_ordinary cursor ~closing:delimiter ~scan ~tag:None ~nesting in
  let stop = cursor.position in
  let is_inside_interpolation position =
    match kind with
    | String { rest; _ } ->
        Array.exists
          (fun ((inner : Token.interpolation), _) ->
            inner.span.start <= position && position < inner.span.stop)
          rest
    | _ -> false
  in
  let rec quote_edits position reversed_edits =
    if position >= stop - 1 then List.rev reversed_edits
    else if Cursor.is_at cursor position '\\' then quote_edits (position + 2) reversed_edits
    else if Cursor.is_at cursor position '"' && not (is_inside_interpolation position) then
      quote_edits (position + 1)
        ({ Syntax_catalog.Lexing.replaced = Source.make_zero_width position; code = Backslash }
        :: reversed_edits)
    else quote_edits (position + 1) reversed_edits
  in
  let template = delimiter = '`' in
  Cursor.report cursor
    ~fixes:
      (if ending = Closed && not (quote_joins_before cursor start) then
         [
           {
             action = Write_between_quotes;
             edits =
               {
                 Syntax_catalog.Lexing.replaced = Source.make_span start (start + 1);
                 code = Quote_marks 1;
               }
               :: quote_edits (start + 1) []
               @ [ { replaced = Source.make_span (stop - 1) stop; code = Quote_marks 1 } ];
           };
         ]
       else [])
    (Source.make_span start (start + 1))
    (if template then Template_literal else Quoted_string);
  (kind, ending)

let lex_curly_quoted_string (cursor : Cursor.t) ~opening_length ~closing =
  let start = cursor.position in
  let text_start = start + opening_length in
  let rest_of_line =
    String.sub cursor.text text_start (Cursor.compute_end_of_line cursor text_start - text_start)
  in
  match String.find_first ~sub:closing rest_of_line with
  | None -> None
  | Some value_length ->
      let value = String.sub rest_of_line 0 value_length in
      let text_stop = text_start + value_length in
      let stop = text_stop + String.length closing in
      let reads_differently =
        String.exists
          (fun character -> character = '\\' || character = '$' || character = '"')
          value
        || quote_joins_before cursor start
      in
      Cursor.report cursor
        ~fixes:
          (if reads_differently then []
           else
             [
               {
                 action = Write_between_quotes;
                 edits =
                   [
                     { replaced = Source.make_span start text_start; code = Quote_marks 1 };
                     { replaced = Source.make_span text_stop stop; code = Quote_marks 1 };
                   ];
               };
             ])
        (Source.make_span start text_start)
        Curly_quote;
      cursor.position <- stop;
      Some
        (Token.String
           {
             tag = None;
             form = Ordinary;
             first = { value; span = Source.make_span text_start text_stop };
             rest = [||];
           })

type scanned = Lexed of (Token.kind * Cursor.ending) | Skipped

let scan (cursor : Cursor.t) ~scan ~nesting =
  let start = cursor.position in
  let is offset character = Cursor.is_at cursor (start + offset) character in
  let make_token (kind, ending) = Some (Lexed (kind, ending)) in
  let make_rejected length problem =
    Source_text.reject cursor ~length problem;
    Some Skipped
  in
  let make_prefixed prefix =
    cursor.position <- start + 1;
    make_token (lex_prefixed_string cursor ~scan ~prefix ~start ~nesting)
  in
  if is 0 '\'' then
    match find_character_literal_end cursor start with
    | Some stop ->
        make_token (lex_character_literal cursor ~tag:"Character" ~literal_start:start ~stop, Closed)
    | None -> (
        let is_apostrophe = touches_word_before cursor start in
        match find_closing_delimiter cursor ~start ~delimiter:'\'' with
        | Some close when (not is_apostrophe) && not (is_name_character cursor (close + 1)) ->
            make_token (lex_quoted_string cursor ~scan ~nesting ~delimiter:'\'')
        | _
          when (not is_apostrophe)
               && Cursor.satisfies cursor (start + 1) (fun next ->
                   Cursor.is_ascii_letter next || next = '_') ->
            let rec locate_name_end position =
              if Cursor.satisfies cursor position Cursor.is_ascii_name_byte then
                locate_name_end (position + 1)
              else position
            in
            make_rejected (locate_name_end (start + 1) - start) Lifetime
        | _ -> make_rejected 1 Apostrophe)
  else if is 0 '`' then
    match find_closing_delimiter cursor ~start ~delimiter:'`' with
    | Some _ -> make_token (lex_quoted_string cursor ~scan ~nesting ~delimiter:'`')
    | None -> make_rejected 1 Backtick
  else if is 0 '@' && is 1 '"' then make_prefixed "@"
  else if is 0 '$' && is 1 '"' then make_prefixed "$"
  else None

let lex_after_name (cursor : Cursor.t) ~scan ~nesting ~start (name : Token.kind) =
  let stop = cursor.position in
  match name with
  | Lower "r" when Cursor.is_at cursor stop '#' ->
      Option.map (fun kind -> (kind, Cursor.Closed)) (hash_raw_string cursor ~start)
  | Lower (("f" | "r" | "b") as prefix)
    when Cursor.is_at cursor stop '"' && (prefix <> "b" || Cursor.run_length cursor stop '"' <= 2)
    ->
      Some (lex_prefixed_string cursor ~scan ~prefix ~start ~nesting)
  | Lower "b" when Cursor.is_at cursor stop '\'' ->
      Option.map
        (fun literal_stop ->
          ( lex_character_literal cursor ~tag:"UInt8" ~literal_start:start ~stop:literal_stop,
            Cursor.Closed ))
        (find_character_literal_end cursor stop ~after_prefix:true)
  | _ -> None

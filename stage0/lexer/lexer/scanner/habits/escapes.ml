let scan (cursor : Cursor.t) buffer =
  let start = cursor.position in
  let parse_hex_value position count =
    let rec are_all_hex_digits index =
      index >= count
      || Cursor.satisfies cursor (position + index) Cursor.is_hexadecimal_digit
         && are_all_hex_digits (index + 1)
    in
    if are_all_hex_digits 0 then Some (int_of_string ("0x" ^ String.sub cursor.text position count))
    else None
  in
  let report_escape stop value =
    Cursor.report cursor
      ~fixes:
        [
          {
            action = Write_escape value;
            edits = [ { replaced = Source.make_span start stop; code = Escapes [ value ] } ];
          };
        ]
      (Source.make_span start stop)
      (Foreign_escape { code_point = value });
    Buffer.add_utf_8_uchar buffer (Uchar.of_int value);
    cursor.position <- stop;
    true
  in
  let check_hex count =
    match parse_hex_value (start + 2) count with
    | Some value when Uchar.is_valid value -> report_escape (start + 2 + count) value
    | _ -> false
  in
  if Cursor.is_at_end cursor (start + 1) then false
  else
    match Cursor.lookup_char cursor (start + 1) with
    | 'u' when not (Cursor.is_at cursor (start + 2) '{') -> check_hex 4
    | 'x' -> check_hex 2
    | 'U' -> check_hex 8
    | 'a' -> report_escape (start + 2) 0x07
    | 'b' -> report_escape (start + 2) 0x08
    | 'f' -> report_escape (start + 2) 0x0C
    | 'v' -> report_escape (start + 2) 0x0B
    | 'e' -> report_escape (start + 2) 0x1B
    | '(' -> (
        let content = start + 2 in
        let rec close position =
          if Cursor.is_at cursor position ')' then Some position
          else if
            Cursor.satisfies cursor position (fun character ->
                Cursor.is_ascii_name_byte character || character = '.')
          then close (position + 1)
          else None
        in
        match close content with
        | Some stop when stop > content ->
            Cursor.report cursor
              ~fixes:
                [
                  {
                    action = Write_interpolation;
                    edits =
                      [
                        { replaced = Source.make_span start content; code = Interpolation_opening };
                        {
                          replaced = Source.make_span stop (stop + 1);
                          code = Interpolation_closing;
                        };
                      ];
                  };
                ]
              (Source.make_span start (stop + 1))
              Parenthesized_interpolation;
            Buffer.add_substring buffer cursor.text start (stop + 1 - start);
            cursor.position <- stop + 1;
            true
        | _ -> false)
    | '\'' ->
        Cursor.report cursor
          ~fixes:
            [
              {
                action = Write_apostrophe;
                edits =
                  [ { replaced = Source.make_span start (start + 2); code = Apostrophe_mark } ];
              };
            ]
          (Source.make_span start (start + 2))
          Escaped_apostrophe;
        Buffer.add_char buffer '\'';
        cursor.position <- start + 2;
        true
    | _ -> false

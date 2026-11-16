let scan (cursor : Cursor.t) buffer =
  let start = cursor.position in
  let hex_value position count =
    let rec all index =
      index >= count
      || (Cursor.satisfies cursor (position + index) Cursor.is_hexadecimal_digit && all (index + 1))
    in
    if all 0 then Some (int_of_string ("0x" ^ String.sub cursor.text position count)) else None
  in
  let is_scalar value = value <= 0x10FFFF && not (value >= 0xD800 && value <= 0xDFFF) in
  let for_character stop value =
    let replacement = Printf.sprintf "\\u{%X}" value in
    Cursor.report cursor ~code:Invalid_escape
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ Diagnostic.replace (Source.span start stop) replacement ];
        ]
      (Source.span start stop)
      (Printf.sprintf
         "`%s` is not an escape in Truss. A character is written by its code point: `%s`."
         (String.sub cursor.text start (stop - start))
         replacement);
    Unicode.encode buffer value;
    cursor.position <- stop;
    true
  in
  let hex count =
    match hex_value (start + 2) count with
    | Some value when is_scalar value -> for_character (start + 2 + count) value
    | _ -> false
  in
  if Cursor.is_at_end cursor (start + 1) then false
  else
    match Cursor.lookup_char cursor (start + 1) with
    | 'u' when not (Cursor.is_at cursor (start + 2) '{') -> hex 4
    | 'x' -> hex 2
    | 'U' -> hex 8
    | 'a' -> for_character (start + 2) 0x07
    | 'b' -> for_character (start + 2) 0x08
    | 'f' -> for_character (start + 2) 0x0C
    | 'v' -> for_character (start + 2) 0x0B
    | 'e' -> for_character (start + 2) 0x1B
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
            Cursor.report cursor ~code:Invalid_escape
              ~fixes:
                [
                  Diagnostic.fix "Write `${...}`"
                    [
                      Diagnostic.replace (Source.span start content) "${";
                      Diagnostic.replace (Source.span stop (stop + 1)) "}";
                    ];
                ]
              (Source.span start (stop + 1))
              "A string interpolates with `${...}`.";
            Buffer.add_substring buffer cursor.text start (stop + 1 - start);
            cursor.position <- stop + 1;
            true
        | _ -> false)
    | '\'' ->
        Cursor.report cursor ~code:Invalid_escape
          ~fixes:
            [
              Diagnostic.fix "Write `'`" [ Diagnostic.replace (Source.span start (start + 2)) "'" ];
            ]
          (Source.span start (start + 2))
          "`'` needs no escape in a string.";
        Buffer.add_char buffer '\'';
        cursor.position <- start + 2;
        true
    | _ -> false

open Cursor

let suffixes =
  [
    ("u8", Some "UInt8");
    ("u16", Some "UInt16");
    ("u32", Some "UInt32");
    ("u64", Some "UInt64");
    ("u128", None);
    ("usize", Some "UInt64");
    ("uz", Some "UInt64");
    ("z", Some "Int64");
    ("i8", Some "Int8");
    ("i16", Some "Int16");
    ("i32", Some "Int32");
    ("i64", Some "Int64");
    ("i128", None);
    ("isize", Some "Int64");
    ("f16", None);
    ("f32", Some "Float32");
    ("f64", Some "Float64");
    ("f128", None);
    ("f", Some "Float32");
    ("d", Some "Float64");
    ("m", None);
    ("u", Some "UInt32");
    ("l", Some "Int64");
    ("ll", Some "Int64");
    ("ul", Some "UInt64");
    ("lu", Some "UInt64");
    ("ull", Some "UInt64");
    ("llu", Some "UInt64");
    ("n", None);
  ]

let is_float_suffix suffix =
  List.mem (String.lowercase_ascii suffix) [ "f"; "d"; "m"; "f16"; "f32"; "f64"; "f128" ]

let is_digit character = character >= '0' && character <= '9'
let is_radix text = String.length text >= 2 && text.[0] = '0' && String.contains "xXbBoO" text.[1]
let is_hexadecimal text = is_radix text && Char.lowercase_ascii text.[1] = 'x'
let is_hexadecimal_digit character = is_digit character || String.contains "abcdefABCDEF" character

let span_of text position accepts =
  let rec loop position =
    if position < String.length text && accepts text.[position] then loop (position + 1)
    else position
  in
  loop position

let scan_end text start =
  let length = String.length text in
  let stop = Numbers.scan_end text start in
  let literal = String.sub text start (stop - start) in
  let digits_only =
    String.for_all (fun character -> is_digit character || character = '_') literal
  in
  let sign_follows stop marker =
    text.[stop - 1] = marker
    && stop + 1 < length
    && (text.[stop] = '+' || text.[stop] = '-')
    && is_digit text.[stop + 1]
  in
  let rec quoted stop =
    if stop + 1 < length && text.[stop] = '\'' && is_digit text.[stop + 1] then
      quoted (Numbers.name_end text (stop + 1))
    else stop
  in
  let stop = if digits_only then quoted stop else stop in
  if is_hexadecimal literal then
    let marker = span_of text (stop + 1) is_hexadecimal_digit in
    let stop =
      if
        stop + 1 < length
        && text.[stop] = '.'
        && marker > stop + 1
        && marker < length
        && (text.[marker] = 'p' || text.[marker] = 'P')
      then Numbers.name_end text (stop + 1)
      else stop
    in
    if sign_follows stop 'p' || sign_follows stop 'P' then Numbers.name_end text (stop + 1)
    else stop
  else if (not (is_radix literal)) && sign_follows stop 'E' then Numbers.name_end text (stop + 1)
  else stop

let number_end text =
  if is_radix text then
    span_of text 2 (fun character -> is_hexadecimal_digit character || character = '_')
  else
    let digits position =
      span_of text position (fun character -> is_digit character || character = '_')
    in
    let whole = digits 0 in
    let position =
      if whole < String.length text && text.[whole] = '.' then digits (whole + 1) else whole
    in
    if position < String.length text && (text.[position] = 'e' || text.[position] = 'E') then
      let digits_start =
        if position + 1 < String.length text && String.contains "+-" text.[position + 1] then
          position + 2
        else position + 1
      in
      let stop = digits digits_start in
      if stop > digits_start then stop else position
    else position

let rec foreign text : Numbers.checked option =
  let length = String.length text in
  let problem code message start stop = Some { Numbers.code; message; start; stop } in
  let translated code message start stop translation =
    let (checked : Numbers.checked) = check translation in
    Some
      {
        Numbers.value = checked.value;
        problem = problem code message start stop;
        fixes =
          (if checked.problem = None then [ ("Write `" ^ translation ^ "`", translation) ] else []);
      }
  in
  let stop = number_end text in
  let suffix = String.sub text stop (length - stop) in
  match String.index_opt text '\'' with
  | Some quote ->
      let grouped =
        String.map (fun character -> if character = '\'' then '_' else character) text
      in
      translated Number_digit_separator
        (Printf.sprintf "Digits are grouped with `_`, as in `%s`." grouped)
        quote (quote + 1) grouped
  | None -> (
      if
        is_hexadecimal text && stop < length
        && (text.[stop] = '.' || text.[stop] = 'p' || text.[stop] = 'P')
      then
        Some
          {
            value = (check (String.sub text 0 stop) : Numbers.checked).value;
            problem =
              problem Number_hexadecimal_float
                "Truss has no hexadecimal floats. Write the value as a decimal float." 0 length;
            fixes = [];
          }
      else if is_radix text && Char.uppercase_ascii text.[1] = text.[1] then
        let prefix = "0" ^ String.make 1 (Char.lowercase_ascii text.[1]) in
        translated Number_uppercase_prefix
          (Printf.sprintf "Number prefixes are lowercase: write `%s`." prefix)
          0 2
          (prefix ^ String.sub text 2 (length - 2))
      else if suffix <> "" && List.mem_assoc (String.lowercase_ascii suffix) suffixes then
        let number = String.sub text 0 stop in
        let value =
          match (check number : Numbers.checked).value with
          | Integer digits when is_float_suffix suffix ->
              Token.Float (Token.Decimal.normalized ~significand:digits ~exponent:Z.zero)
          | value -> value
        in
        let type_name =
          match List.assoc (String.lowercase_ascii suffix) suffixes with
          | Some type_name -> type_name
          | None ->
              if String.contains number '.' || String.contains number 'e' then "Float64"
              else "Int64"
        in
        Some
          {
            value;
            problem =
              problem Number_suffix
                (Printf.sprintf
                   "Number literals have no type suffixes such as `%s`. A literal takes its type \
                    from its context, as in `let value: %s = %s`."
                   suffix type_name number)
                stop length;
            fixes = [];
          }
      else
        match String.index_opt text 'E' with
        | Some marker when (not (is_radix text)) && marker < stop ->
            translated Number_uppercase_exponent "The exponent is written with a lowercase `e`."
              marker (marker + 1)
              (String.mapi (fun index character -> if index = marker then 'e' else character) text)
        | _ ->
            let whole = span_of text 0 (fun character -> is_digit character || character = '_') in
            let digits = String.concat "" (String.split_on_char '_' (String.sub text 0 whole)) in
            if is_radix text || String.length digits < 2 || digits.[0] <> '0' then None
            else
              let without_zeros =
                let stripped =
                  span_of text 0 (fun character -> character = '0' || character = '_')
                in
                if stripped >= whole then "0" else String.sub text stripped (whole - stripped)
              in
              let decimal = without_zeros ^ String.sub text whole (length - whole) in
              let octal_possible =
                whole = length
                && String.for_all (fun character -> character >= '0' && character <= '7') digits
              in
              let clean translation = (check translation : Numbers.checked).problem = None in
              let alternatives =
                if octal_possible then
                  let octal = "0o" ^ without_zeros in
                  if clean octal && clean decimal then
                    [
                      ("Write `" ^ octal ^ "` (octal)", octal);
                      ("Write `" ^ decimal ^ "` (decimal)", decimal);
                    ]
                  else []
                else if clean decimal then [ ("Write `" ^ decimal ^ "`", decimal) ]
                else []
              in
              Some
                {
                  value = (check decimal : Numbers.checked).value;
                  problem =
                    problem Number_leading_zero
                      (if octal_possible then
                         Printf.sprintf
                           "Decimal numbers do not start with `0`. In C and Go, `%s` would be \
                            octal: write `0o%s` for octal, or `%s` for decimal."
                           (String.sub text 0 whole) without_zeros without_zeros
                       else "Decimal numbers do not start with `0`.")
                      0 whole;
                  fixes = alternatives;
                })

and check text = match foreign text with Some checked -> checked | None -> Numbers.check text

let trailing_point cursor ~start ~stop (checked : Numbers.checked) =
  match checked with
  | { value = Integer _; problem = None; _ }
    when is_at cursor stop '.' && not (is_radix (String.sub cursor.text start (stop - start))) -> (
      match check (String.sub cursor.text start (stop + 1 - start) ^ "0") with
      | { value = Float _ as value; problem = None; _ } -> Some value
      | _ -> None)
  | _ -> None

let report_trailing_point cursor ~start ~point =
  let written = String.sub cursor.text start (point + 1 - start) in
  report cursor ~code:Number_missing_digits
    ~fixes:(code_fixes cursor (span start (point + 1)) [ written ^ "0" ])
    (span point (point + 1))
    (Printf.sprintf "A float has a digit after its `.`: `%s0`." written)

let leading_dot cursor =
  let start = cursor.position in
  let stop = scan_end cursor.text (start + 1) in
  let written = String.sub cursor.text start (stop - start) in
  let checked = check ("0" ^ written) in
  match checked.value with
  | Float _ ->
      cursor.position <- stop;
      let fixed = "0" ^ written in
      let fixes, message =
        match checked.problem with
        | None ->
            ( code_fixes cursor (span start stop) [ fixed ],
              Printf.sprintf "A float has a digit before its `.`: `%s`." fixed )
        | Some _ -> ([], "A float has a digit before its `.`.")
      in
      report cursor ~code:Number_missing_digits ~fixes (span start (start + 1)) message;
      Some checked.value
  | _ -> None

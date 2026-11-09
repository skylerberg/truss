(* Number literals. A number is scanned wide and then checked, so that `3u8`,
   `0xFG`, `1_`, and `0b102` each become one token with one precise error
   (LEXER.md, "Numbers").

   A literal with several problems gets one diagnostic, for the leftmost
   problem, and its fix corrects all of them at once, so that applying it
   leaves no error behind. A literal with a problem that has no exact fix,
   such as a digit its base does not allow, gets no fix. *)

type value = Integer of Z.t | Float of { significand : Z.t; exponent : Z.t }

type problem = {
  code : string;
  message : string;
  start : int;  (* offsets within the literal *)
  stop : int;
}

type checked = {
  value : value;
  problem : problem option;
  fixes : (string * string) list;  (* title, replacement for the whole literal *)
}

let is_digit c = c >= '0' && c <= '9'
let is_ascii_word c = is_digit c || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'

let is_radix_prefix text start =
  start + 1 < String.length text
  && text.[start] = '0'
  && match text.[start + 1] with 'x' | 'X' | 'b' | 'B' | 'o' | 'O' -> true | _ -> false

(* The end of the number that starts at [start], following LEXER.md's
   steps. The run also takes in name characters outside ASCII, so that `3é`
   is one token with one error. *)
let scan_end text start =
  let length = String.length text in
  let rec run position =
    if position >= length then position
    else if is_ascii_word text.[position] then run (position + 1)
    else if Char.code text.[position] >= 0x80 then
      let packed = Unicode.decode text position in
      if packed >= 0 && Unicode.is_xid_continue (Unicode.decoded_code_point packed) then
        run (position + Unicode.decoded_length packed)
      else position
    else position
  in
  let stop = run start in
  let only_digits = ref true in
  for index = start to stop - 1 do
    if not (is_digit text.[index] || text.[index] = '_') then only_digits := false
  done;
  let stop =
    if !only_digits && stop + 1 < length && text.[stop] = '.' && is_digit text.[stop + 1] then
      run (stop + 1)
    else stop
  in
  if
    (not (is_radix_prefix text start))
    && (text.[stop - 1] = 'e' || text.[stop - 1] = 'E')
    && stop + 1 < length
    && (text.[stop] = '+' || text.[stop] = '-')
    && is_digit text.[stop + 1]
  then run (stop + 1)
  else stop

(* Type suffixes from other languages, and the Truss type each one means. *)
let suffixes =
  [
    ("u8", Some "UInt8"); ("u16", Some "UInt16"); ("u32", Some "UInt32"); ("u64", Some "UInt64");
    ("u128", None); ("usize", Some "USize"); ("uz", Some "USize"); ("z", Some "ISize");
    ("i8", Some "Int8"); ("i16", Some "Int16"); ("i32", Some "Int32"); ("i64", Some "Int64");
    ("i128", None); ("isize", Some "ISize");
    ("f16", None); ("f32", Some "Float32"); ("f64", Some "Float64"); ("f128", None);
    ("f", Some "Float32"); ("d", Some "Float64"); ("m", None);
    ("u", Some "UInt32"); ("l", Some "Int64"); ("ll", Some "Int64"); ("ul", Some "UInt64");
    ("lu", Some "UInt64"); ("ull", Some "UInt64"); ("llu", Some "UInt64"); ("n", None);
  ]

let suffix_type text = List.assoc_opt (String.lowercase_ascii text) suffixes

let is_float_suffix text =
  match String.lowercase_ascii text with
  | "f" | "d" | "m" | "f16" | "f32" | "f64" | "f128" -> true
  | _ -> false

(* A group of digits with `_` only singly and between digits, and the offset
   of the first misplaced `_`, if any. *)
let clean_underscores group =
  let parts = List.filter (fun part -> part <> "") (String.split_on_char '_' group) in
  let cleaned = String.concat "_" parts in
  if cleaned = group then (cleaned, None)
  else
    let length = String.length group in
    let rec first_bad index =
      if index >= length then None
      else if
        group.[index] = '_'
        && (index = 0 || index = length - 1 || group.[index + 1] = '_')
      then Some index
      else first_bad (index + 1)
    in
    (cleaned, first_bad 0)

let without_underscores group = String.concat "" (String.split_on_char '_' group)

type issue = { problem : problem; fixable : bool }

let issue ?(fixable = true) code message start stop =
  { problem = { code; message; start; stop }; fixable }

let base_name = function 16 -> "hexadecimal" | 2 -> "binary" | _ -> "octal"

let is_digit_of_base base c =
  match base with
  | 16 -> is_digit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
  | 2 -> c = '0' || c = '1'
  | _ -> c >= '0' && c <= '7'

(* The length of the character at [offset], for pointing at it. *)
let character_length text offset =
  let packed = Unicode.decode text offset in
  if packed < 0 then 1 else Unicode.decoded_length packed

let character_at text offset = String.sub text offset (character_length text offset)

let suffix_issue text ~at ~fixed =
  let suffix = String.sub text at (String.length text - at) in
  let example =
    match suffix_type suffix with
    | Some (Some type_name) -> Printf.sprintf "`let value: %s = %s`" type_name fixed
    | _ ->
        let default_type = if String.contains fixed '.' || String.contains fixed 'e' then "Float64" else "Int64" in
        Printf.sprintf "`let value: %s = %s`" default_type fixed
  in
  issue "lexer.number_suffix"
    (Printf.sprintf
       "Number literals have no type suffixes such as `%s`. A literal takes its type from its \
        context, as in %s."
       suffix example)
    at (String.length text)

let underscore_issue at =
  issue "lexer.number_underscore" "`_` can only go between digits." at (at + 1)

(* Picks the problem to report: the leftmost one without an exact fix if
   there is one, and otherwise the leftmost one, with a fix for them all. *)
let decide value issues fixes =
  let leftmost issues =
    List.fold_left
      (fun best candidate ->
        match best with
        | Some best when best.problem.start <= candidate.problem.start -> Some best
        | _ -> Some candidate)
      None issues
  in
  match List.filter (fun issue -> not issue.fixable) issues with
  | _ :: _ as unfixable -> { value; problem = Option.map (fun i -> i.problem) (leftmost unfixable); fixes = [] }
  | [] -> (
      match leftmost issues with
      | None -> { value; problem = None; fixes = [] }
      | Some first -> { value; problem = Some first.problem; fixes = fixes () })

let check_radix text =
  let length = String.length text in
  let letter = text.[1] in
  let base = match Char.lowercase_ascii letter with 'x' -> 16 | 'b' -> 2 | _ -> 8 in
  let digits_end =
    let rec loop index =
      if index < length && (is_digit_of_base base text.[index] || text.[index] = '_') then
        loop (index + 1)
      else index
    in
    loop 2
  in
  let group = String.sub text 2 (digits_end - 2) in
  let cleaned, bad_underscore = clean_underscores group in
  let digits = without_underscores group in
  let prefix = Printf.sprintf "0%c" (Char.lowercase_ascii letter) in
  let fixed = prefix ^ cleaned in
  let rest = String.sub text digits_end (length - digits_end) in
  let rest_is_suffix = rest <> "" && suffix_type rest <> None in
  let issues =
    List.concat
      [
        (if letter <> Char.lowercase_ascii letter then
           [
             issue "lexer.number_uppercase_prefix"
               (Printf.sprintf "Number prefixes are lowercase: write `%s`." prefix)
               0 2;
           ]
         else []);
        (if digits = "" && (rest = "" || rest_is_suffix) then
           [
             issue ~fixable:false "lexer.number_missing_digits"
               (Printf.sprintf "`%s` must be followed by %s digits." prefix (base_name base))
               0 digits_end;
           ]
         else []);
        (match bad_underscore with
        | Some offset when digits <> "" -> [ underscore_issue (2 + offset) ]
        | _ -> []);
        (if rest <> "" then
           if rest_is_suffix then
             if digits = "" then [] else [ suffix_issue text ~at:digits_end ~fixed ]
           else
             [
               issue ~fixable:false "lexer.number_invalid_digit"
                 (Printf.sprintf "`%s` is not a %s digit." (character_at text digits_end)
                    (base_name base))
                 digits_end
                 (digits_end + character_length text digits_end);
             ]
         else []);
      ]
  in
  let value = Integer (if digits = "" then Z.zero else Z.of_string_base base digits) in
  decide value issues (fun () -> [ ("Write `" ^ fixed ^ "`", fixed) ])

let check_decimal text =
  let length = String.length text in
  let digits_from start =
    let rec loop index =
      if index < length && (is_digit text.[index] || text.[index] = '_') then loop (index + 1)
      else index
    in
    loop start
  in
  let whole_end = digits_from 0 in
  let whole = String.sub text 0 whole_end in
  let fraction, position =
    if whole_end < length && text.[whole_end] = '.' then
      let stop = digits_from (whole_end + 1) in
      (Some (String.sub text (whole_end + 1) (stop - whole_end - 1), whole_end + 1), stop)
    else (None, whole_end)
  in
  (* The exponent: its marker, sign, digits, and where its digits start. *)
  let exponent, rest_start =
    if position < length && (text.[position] = 'e' || text.[position] = 'E') then
      let marker = text.[position] in
      let after_sign =
        if position + 1 < length && (text.[position + 1] = '+' || text.[position + 1] = '-') then
          position + 2
        else position + 1
      in
      let stop = digits_from after_sign in
      let sign = String.sub text (position + 1) (after_sign - position - 1) in
      if stop = after_sign && stop < length then (None, position)
      else (Some (marker, sign, String.sub text after_sign (stop - after_sign), position, after_sign), stop)
    else (None, position)
  in
  let rest = String.sub text rest_start (length - rest_start) in
  let whole_cleaned, whole_bad = clean_underscores whole in
  let whole_digits = without_underscores whole in
  let fraction_cleaned =
    Option.map (fun (group, start) -> (clean_underscores group, start)) fraction
  in
  let exponent_cleaned =
    Option.map
      (fun (marker, sign, group, at, digits_start) -> (marker, sign, clean_underscores group, group, at, digits_start))
      exponent
  in
  let is_float = fraction <> None || exponent <> None in
  let has_float_suffix = rest <> "" && is_float_suffix rest in
  (* The literal with every fixable problem corrected, given the whole part
     to use. *)
  let assemble whole_part =
    let fraction_part =
      match fraction_cleaned with Some ((cleaned, _), _) -> "." ^ cleaned | None -> ""
    in
    let exponent_part =
      match exponent_cleaned with
      | Some (_, sign, (cleaned, _), _, _, _) -> "e" ^ sign ^ cleaned
      | None -> ""
    in
    let float_part = if has_float_suffix && not is_float then ".0" else "" in
    whole_part ^ fraction_part ^ exponent_part ^ float_part
  in
  let leading_zero = String.length whole_digits > 1 && whole_digits.[0] = '0' in
  let without_zeros =
    let rec first_nonzero index =
      if index >= String.length whole_cleaned then None
      else if whole_cleaned.[index] <> '0' && whole_cleaned.[index] <> '_' then Some index
      else first_nonzero (index + 1)
    in
    match first_nonzero 0 with
    | Some index -> String.sub whole_cleaned index (String.length whole_cleaned - index)
    | None -> "0"
  in
  let octal_possible =
    leading_zero && (not is_float) && (not has_float_suffix)
    && String.for_all (fun c -> c >= '0' && c <= '7') whole_digits
  in
  let fixed = assemble (if leading_zero then without_zeros else whole_cleaned) in
  let issues =
    List.concat
      [
        (if leading_zero then
           [
             issue "lexer.number_leading_zero"
               (if octal_possible then
                  Printf.sprintf
                    "Decimal numbers do not start with `0`. In C and Go, `%s` would be octal: \
                     write `0o%s` for octal, or `%s` for decimal."
                    whole without_zeros without_zeros
                else "Decimal numbers do not start with `0`.")
               0 whole_end;
           ]
         else []);
        (match whole_bad with Some offset -> [ underscore_issue offset ] | None -> []);
        (match fraction_cleaned with
        | Some ((_, Some offset), start) -> [ underscore_issue (start + offset) ]
        | _ -> []);
        (match exponent_cleaned with
        | Some (marker, _, (_, bad), group, at, digits_start) ->
            List.concat
              [
                (if marker = 'E' then
                   [ issue "lexer.number_uppercase_exponent" "The exponent is written with a lowercase `e`." at (at + 1) ]
                 else []);
                (if without_underscores group = "" then
                   [
                     issue ~fixable:false "lexer.number_missing_digits" "The exponent needs digits after `e`."
                       at digits_start;
                   ]
                 else match bad with Some offset -> [ underscore_issue (digits_start + offset) ] | None -> []);
              ]
        | None -> []);
        (if rest = "" then []
         else if suffix_type rest <> None then [ suffix_issue text ~at:rest_start ~fixed ]
         else
           [
             issue ~fixable:false "lexer.number_followed_by_name"
               (Printf.sprintf "A number cannot be followed directly by a name character such as `%s`."
                  (character_at text rest_start))
               rest_start
               (rest_start + character_length text rest_start);
           ]);
      ]
  in
  let value =
    if not is_float then Integer (Z.of_string whole_digits)
    else
      let fraction_digits =
        match fraction with Some (group, _) -> without_underscores group | None -> ""
      in
      let written_exponent =
        match exponent with
        | Some (_, sign, group, _, _) when without_underscores group <> "" ->
            let magnitude = Z.of_string (without_underscores group) in
            if sign = "-" then Z.neg magnitude else magnitude
        | _ -> Z.zero
      in
      let significand = Z.of_string (whole_digits ^ fraction_digits) in
      let exponent = Z.sub written_exponent (Z.of_int (String.length fraction_digits)) in
      (* Remove trailing zeros, so that equal values are stored the same way. *)
      let ten = Z.of_int 10 in
      let rec normalize significand exponent =
        if Z.equal significand Z.zero then (Z.zero, Z.zero)
        else
          let quotient, remainder = Z.div_rem significand ten in
          if Z.equal remainder Z.zero then normalize quotient (Z.succ exponent)
          else (significand, exponent)
      in
      let significand, exponent = normalize significand exponent in
      Float { significand; exponent }
  in
  decide value issues (fun () ->
      if octal_possible then
        let octal = assemble ("0o" ^ without_zeros) in
        [ ("Write `" ^ octal ^ "` (octal)", octal); ("Write `" ^ fixed ^ "` (decimal)", fixed) ]
      else [ ("Write `" ^ fixed ^ "`", fixed) ])

let check text = if is_radix_prefix text 0 then check_radix text else check_decimal text

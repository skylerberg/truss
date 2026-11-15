type problem = { code : Diagnostic.Code.lexer; message : string; start : int; stop : int }
type checked = { value : Token.kind; problem : problem option; fixes : (string * string) list }

let is_digit character = character >= '0' && character <= '9'

let is_hexadecimal_digit character =
  is_digit character
  || (character >= 'a' && character <= 'f')
  || (character >= 'A' && character <= 'F')

let is_radix_prefix text start =
  start + 1 < String.length text
  && text.[start] = '0'
  && match text.[start + 1] with 'x' | 'b' | 'o' -> true | _ -> false

let name_end text position =
  let length = String.length text in
  let rec loop position =
    if position >= length then position
    else
      match text.[position] with
      | '0' .. '9' | 'a' .. 'z' | 'A' .. 'Z' | '_' -> loop (position + 1)
      | character when Char.code character >= 0x80 ->
          let decoded = Unicode.decode text position in
          if
            Unicode.Decoded.is_valid decoded
            && Unicode.is_xid_continue (Unicode.Decoded.code_point decoded)
          then loop (position + Unicode.Decoded.length decoded)
          else position
      | _ -> position
  in
  loop position

let scan_end text start =
  let length = String.length text in
  let stop = name_end text start in
  let only_digits =
    String.for_all
      (fun character -> is_digit character || character = '_')
      (String.sub text start (stop - start))
  in
  let stop =
    if only_digits && stop + 1 < length && text.[stop] = '.' && is_digit text.[stop + 1] then
      name_end text (stop + 1)
    else stop
  in
  if
    (not (is_radix_prefix text start))
    && text.[stop - 1] = 'e'
    && stop + 1 < length
    && (text.[stop] = '+' || text.[stop] = '-')
    && is_digit text.[stop + 1]
  then name_end text (stop + 1)
  else stop

let clean_underscores group =
  let parts = List.filter (fun part -> part <> "") (String.split_on_char '_' group) in
  let cleaned = String.concat "_" parts in
  if cleaned = group then (cleaned, None)
  else
    let length = String.length group in
    let rec first_bad index =
      if index >= length then None
      else if group.[index] = '_' && (index = 0 || index = length - 1 || group.[index + 1] = '_')
      then Some index
      else first_bad (index + 1)
    in
    (cleaned, first_bad 0)

let without_underscores group = String.concat "" (String.split_on_char '_' group)

type issue = { problem : problem; fixable : bool }

let issue ?(fixable = true) code message start stop =
  { problem = { code; message; start; stop }; fixable }

let underscore_issue offset =
  issue Number_underscore "`_` can only go between digits." offset (offset + 1)

let character_length text offset =
  let decoded = Unicode.decode text offset in
  if Unicode.Decoded.is_valid decoded then Unicode.Decoded.length decoded else 1

let choose_problem value issues ~fixed =
  let leftmost issues =
    List.fold_left
      (fun best candidate ->
        match best with
        | Some best when best.problem.start <= candidate.problem.start -> Some best
        | _ -> Some candidate)
      None issues
  in
  match List.filter (fun issue -> not issue.fixable) issues with
  | _ :: _ as unfixable ->
      { value; problem = Option.map (fun issue -> issue.problem) (leftmost unfixable); fixes = [] }
  | [] -> (
      match leftmost issues with
      | None -> { value; problem = None; fixes = [] }
      | Some first ->
          { value; problem = Some first.problem; fixes = [ ("Write `" ^ fixed ^ "`", fixed) ] })

let check_radix text =
  let length = String.length text in
  let base, name =
    match text.[1] with 'x' -> (16, "hexadecimal") | 'b' -> (2, "binary") | _ -> (8, "octal")
  in
  let is_base_digit character =
    match base with
    | 16 -> is_hexadecimal_digit character
    | 2 -> character = '0' || character = '1'
    | _ -> character >= '0' && character <= '7'
  in
  let rec digits_end index =
    if index < length && (is_base_digit text.[index] || text.[index] = '_') then
      digits_end (index + 1)
    else index
  in
  let stop = digits_end 2 in
  let group = String.sub text 2 (stop - 2) in
  let cleaned, bad_underscore = clean_underscores group in
  let digits = without_underscores group in
  let issues =
    List.concat
      [
        (if digits = "" && stop = length then
           [
             issue ~fixable:false Number_missing_digits
               (Printf.sprintf "`%s` must be followed by %s digits." (String.sub text 0 2) name)
               0 stop;
           ]
         else []);
        (match bad_underscore with
        | Some offset when digits <> "" -> [ underscore_issue (2 + offset) ]
        | _ -> []);
        (if stop < length then
           [
             issue ~fixable:false Number_invalid_digit
               (Printf.sprintf "`%s` is not a %s digit."
                  (String.sub text stop (character_length text stop))
                  name)
               stop
               (stop + character_length text stop);
           ]
         else []);
      ]
  in
  let value = Token.Integer (if digits = "" then Z.zero else Z.of_string_base base digits) in
  choose_problem value issues ~fixed:(String.sub text 0 2 ^ cleaned)

let check_decimal text =
  let length = String.length text in
  let group_from offset =
    let rec stop index =
      if index < length && (is_digit text.[index] || text.[index] = '_') then stop (index + 1)
      else index
    in
    (offset, String.sub text offset (stop offset - offset))
  in
  let after (offset, group) = offset + String.length group in
  let whole = group_from 0 in
  let fraction =
    if after whole < length && text.[after whole] = '.' then Some (group_from (after whole + 1))
    else None
  in
  let position = match fraction with Some fraction -> after fraction | None -> after whole in
  let exponent =
    if position < length && text.[position] = 'e' then
      let digits_offset =
        if position + 1 < length && (text.[position + 1] = '+' || text.[position + 1] = '-') then
          position + 2
        else position + 1
      in
      let digits = group_from digits_offset in
      if snd digits = "" && digits_offset < length then None
      else Some (position, String.sub text (position + 1) (digits_offset - position - 1), digits)
    else None
  in
  let rest = match exponent with Some (_, _, digits) -> after digits | None -> position in
  let underscore (offset, group) =
    match snd (clean_underscores group) with
    | Some bad -> [ underscore_issue (offset + bad) ]
    | None -> []
  in
  let cleaned (_, group) = fst (clean_underscores group) in
  let issues =
    List.concat
      [
        underscore whole;
        Option.fold ~none:[] ~some:underscore fraction;
        (match exponent with
        | Some (marker, _, digits) ->
            if without_underscores (snd digits) = "" then
              [
                issue ~fixable:false Number_missing_digits "The exponent needs digits after `e`."
                  marker (fst digits);
              ]
            else underscore digits
        | None -> []);
        (if rest < length then
           [
             issue ~fixable:false Number_followed_by_name
               (Printf.sprintf
                  "A number cannot be followed directly by a name character such as `%s`."
                  (String.sub text rest (character_length text rest)))
               rest
               (rest + character_length text rest);
           ]
         else []);
      ]
  in
  let fixed =
    cleaned whole
    ^ Option.fold ~none:"" ~some:(fun fraction -> "." ^ cleaned fraction) fraction
    ^ Option.fold ~none:"" ~some:(fun (_, sign, digits) -> "e" ^ sign ^ cleaned digits) exponent
  in
  let whole_digits = without_underscores (snd whole) in
  let value =
    if fraction = None && exponent = None then Token.Integer (Z.of_string whole_digits)
    else
      let fraction_digits =
        Option.fold ~none:"" ~some:(fun (_, group) -> without_underscores group) fraction
      in
      let exponent_value =
        match exponent with
        | Some (_, sign, (_, group)) when without_underscores group <> "" ->
            let magnitude = Z.of_string (without_underscores group) in
            if sign = "-" then Z.neg magnitude else magnitude
        | _ -> Z.zero
      in
      Token.Float
        (Token.Decimal.normalized
           ~significand:(Z.of_string (whole_digits ^ fraction_digits))
           ~exponent:(Z.sub exponent_value (Z.of_int (String.length fraction_digits))))
  in
  choose_problem value issues ~fixed

let check text = if is_radix_prefix text 0 then check_radix text else check_decimal text

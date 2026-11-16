type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string;
  problem : (Diagnostic.Code.lexer * string) option;
  fix : string option;
}

let is_upper character = character >= 'A' && character <= 'Z'
let is_lower character = character >= 'a' && character <= 'z'

let classify_name name =
  match
    String.fold_left
      (fun first character ->
        match first with None when character <> '_' -> Some character | first -> first)
      None name
  with
  | Some first when is_upper first -> Upper
  | _ -> Lower

let split_name name = List.filter (fun part -> part <> "") (String.split_on_char '_' name)

let to_snake name =
  let length = String.length name in
  let buffer = Buffer.create (length + 4) in
  String.iteri
    (fun index character ->
      if is_upper character then begin
        let starts_word =
          index > 0
          &&
          let previous = name.[index - 1] in
          previous <> '_'
          && ((not (is_upper previous)) || (index + 1 < length && is_lower name.[index + 1]))
        in
        if starts_word then Buffer.add_char buffer '_';
        Buffer.add_char buffer (Char.lowercase_ascii character)
      end
      else Buffer.add_char buffer character)
    name;
  String.concat "_" (split_name (Buffer.contents buffer))

let to_camel name =
  String.concat ""
    (List.mapi
       (fun index part -> if index = 0 then part else String.capitalize_ascii part)
       (split_name name))

let correct_case name =
  match split_name name with
  | [] -> name
  | first :: _ when is_upper first.[0] ->
      if not (String.contains name '_') then name
      else if not (String.exists is_lower name) then
        String.lowercase_ascii (String.concat "_" (split_name name))
      else to_camel name
  | _ -> to_snake name

let find_case_problem name =
  let length = String.length name in
  let rec has_double_underscore index =
    index + 1 < length
    && ((name.[index] = '_' && name.[index + 1] = '_') || has_double_underscore (index + 1))
  in
  let message =
    if length > 0 && name.[0] = '_' then Some "Names cannot start with `_`."
    else if classify_name name = Upper then
      if not (String.contains name '_') then None
      else if not (String.exists is_lower name) then
        Some
          (Printf.sprintf
             "`%s` is written like a constant from another language. Constants are values, so \
              their names are lower_snake_case."
             name)
      else Some "A name that starts with an uppercase letter is UpperCamelCase, with no `_`."
    else if String.exists is_upper name then
      Some
        "A name that starts with a lowercase letter is lower_snake_case, with no uppercase letters."
    else if length > 0 && name.[length - 1] = '_' then Some "Names cannot end with `_`."
    else if has_double_underscore 0 then
      Some "`_` appears only singly, between the parts of a name."
    else None
  in
  Option.map (fun message -> (Diagnostic.Code.Name_case, message)) message

let find_first_non_ascii name =
  let rec find index =
    if index >= String.length name then None
    else if Char.code name.[index] >= 0x80 then
      let decoded = Unicode.decode name index in
      Some
        (Printf.sprintf "`%s` (U+%04X)"
           (String.sub name index (Unicode.Decoded.length decoded))
           (Unicode.Decoded.code_point decoded))
    else find (index + 1)
  in
  find 0

let check name =
  match find_first_non_ascii name with
  | Some character ->
      {
        kind = classify_name name;
        name;
        problem =
          Some
            ( Diagnostic.Code.Name_not_ascii,
              Printf.sprintf
                "Names use only ASCII letters, digits, and `_`, and %s is not ASCII. Text in any \
                 language goes in strings."
                character );
        fix = None;
      }
  | None -> (
      match find_case_problem name with
      | None -> { kind = classify_name name; name; problem = None; fix = None }
      | Some problem ->
          let corrected = correct_case name in
          let fix =
            if
              corrected <> name && corrected <> ""
              && (is_upper corrected.[0] || is_lower corrected.[0])
              && find_case_problem corrected = None
              && Token.find_word corrected = None
            then Some corrected
            else None
          in
          { kind = classify_name name; name; problem = Some problem; fix })

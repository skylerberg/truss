type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string;
  problem : Syntax_catalog.Lexing.name_problem option;
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

let find_case_problem name : Syntax_catalog.Lexing.name_problem option =
  if String.starts_with ~prefix:"_" name then Some Leading_underscore
  else if classify_name name = Upper then
    if not (String.contains name '_') then None
    else if not (String.exists is_lower name) then Some (Constant_case name)
    else Some Upper_with_underscore
  else if String.exists is_upper name then Some Lower_with_upper
  else if String.ends_with ~suffix:"_" name then Some Trailing_underscore
  else if String.includes ~affix:"__" name then Some Doubled_underscore
  else None

let find_first_non_ascii name : Syntax_catalog.Lexing.character option =
  Option.map
    (fun index ->
      let decoded = String.get_utf_8_uchar name index in
      Syntax_catalog.Lexing.Unicode
        {
          text = String.sub name index (Uchar.utf_decode_length decoded);
          code_point = Uchar.to_int (Uchar.utf_decode_uchar decoded);
        })
    (String.find_first_index (Fun.negate Char.Ascii.is_valid) name)

let check name =
  match find_first_non_ascii name with
  | Some character ->
      { kind = classify_name name; name; problem = Some (Not_ascii character); fix = None }
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

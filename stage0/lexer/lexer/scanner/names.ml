(* The checks on each name on its own: that it is ASCII, and the case rules.

   A name with a problem gets one diagnostic, for the first check it fails.
   A case problem has a fix that rewrites the name to pass every check. A
   letter outside ASCII has none, since no spelling can be chosen for the
   author. The fix depends only on the name, so every use of a misspelled
   name gets the same fix. *)

type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string; (* the corrected name when there is a fix *)
  problem : (Diagnostic.Code.lexer * string) option; (* code, message *)
  fix : string option;
}

let is_upper c = c >= 'A' && c <= 'Z'
let is_lower c = c >= 'a' && c <= 'z'

let kind_of name =
  match
    String.fold_left
      (fun first c -> match first with None when c <> '_' -> Some c | first -> first)
      None name
  with
  | Some first when is_upper first -> Upper
  | _ -> Lower

(* The parts of a name between `_`s, leaving out empty ones. *)
let parts name = List.filter (fun part -> part <> "") (String.split_on_char '_' name)

(* `userName` and `parseHTTPResponse` become `user_name` and
   `parse_http_response`: a `_` goes before an uppercase letter that follows
   a lowercase letter or digit, or that starts a new word after an acronym. *)
let to_snake name =
  let length = String.length name in
  let buffer = Buffer.create (length + 4) in
  String.iteri
    (fun index c ->
      if is_upper c then begin
        let starts_word =
          index > 0
          &&
          let previous = name.[index - 1] in
          previous <> '_'
          && ((not (is_upper previous)) || (index + 1 < length && is_lower name.[index + 1]))
        in
        if starts_word then Buffer.add_char buffer '_';
        Buffer.add_char buffer (Char.lowercase_ascii c)
      end
      else Buffer.add_char buffer c)
    name;
  String.concat "_" (parts (Buffer.contents buffer))

(* `Http_client` becomes `HttpClient`. *)
let to_camel name =
  String.concat ""
    (List.mapi
       (fun index part -> if index = 0 then part else String.capitalize_ascii part)
       (parts name))

let correct_case name =
  match parts name with
  | [] -> name
  | first :: _ when is_upper first.[0] ->
      if not (String.contains name '_') then name
      else if not (String.exists is_lower name) then
        String.lowercase_ascii (String.concat "_" (parts name))
      else to_camel name
  | _ -> to_snake name

let case_problem name =
  let length = String.length name in
  let rec has_double_underscore index =
    index + 1 < length
    && ((name.[index] = '_' && name.[index + 1] = '_') || has_double_underscore (index + 1))
  in
  let message =
    if length > 0 && name.[0] = '_' then Some "Names cannot start with `_`."
    else if kind_of name = Upper then
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

(* The first character outside ASCII, described for a message. The scanner
   gives only valid UTF-8 here. *)
let first_non_ascii name =
  let rec find index =
    if index >= String.length name then None
    else if Char.code name.[index] >= 0x80 then
      let packed = Unicode.decode name index in
      Some
        (Printf.sprintf "`%s` (U+%04X)"
           (String.sub name index (Unicode.decoded_length packed))
           (Unicode.decoded_code_point packed))
    else find (index + 1)
  in
  find 0

let check name =
  match first_non_ascii name with
  | Some character ->
      {
        kind = kind_of name;
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
      match case_problem name with
      | None -> { kind = kind_of name; name; problem = None; fix = None }
      | Some problem ->
          let corrected = correct_case name in
          let fix =
            if
              corrected <> name && corrected <> ""
              && (is_upper corrected.[0] || is_lower corrected.[0])
              && case_problem corrected = None
              && Token.word corrected = None
            then Some corrected
            else None
          in
          let name = Option.value fix ~default:name in
          { kind = kind_of name; name; problem = Some problem; fix })

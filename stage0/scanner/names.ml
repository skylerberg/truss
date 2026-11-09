(* The checks on each name on its own (LEXER.md, "Names and keywords"): case
   rules, Normalization Form C, allowed characters, and scripts.

   A name with a problem gets one diagnostic, for the first check it fails.
   Its fix rewrites the name to pass every check, or there is no fix when no
   rewrite can: the case rules and NFC can be corrected, but a character that
   is not allowed or a mix of scripts cannot. The fix depends only on the
   name, so every use of a misspelled name gets the same fix. *)

type kind = Upper | Lower

type checked = {
  kind : kind;
  name : string;  (* the corrected name when there is a fix *)
  problem : (string * string) option;  (* code, message *)
  fix : string option;
}

let underscore = Char.code '_'
let is_ascii text = String.for_all (fun c -> Char.code c < 0x80) text
let is_upper = Unicode.is_uppercase_or_titlecase

(* A character that has an uppercase form, such as `a` or `é`. *)
let is_lowercase_letter value = Unicode.to_uppercase value <> value

let kind_of code_points =
  match List.filter (fun value -> value <> underscore) code_points with
  | first :: _ when is_upper first -> Upper
  | _ -> Lower

let rec drop_underscores = function
  | value :: rest when value = underscore -> drop_underscores rest
  | values -> values

(* Splits on `_`, dropping empty parts. *)
let parts code_points =
  let rec loop current parts = function
    | [] -> List.rev (if current = [] then parts else List.rev current :: parts)
    | value :: rest when value = underscore ->
        loop [] (if current = [] then parts else List.rev current :: parts) rest
    | value :: rest -> loop (value :: current) parts rest
  in
  loop [] [] code_points

let join_snake parts = List.concat (List.mapi (fun index part -> if index = 0 then part else underscore :: part) parts)

(* `userName` and `parseHTTPResponse` become `user_name` and
   `parse_http_response`: a `_` goes before an uppercase letter that follows
   a lowercase letter or digit, or that starts a new word after an acronym. *)
let to_snake code_points =
  let array = Array.of_list code_points in
  let length = Array.length array in
  let output = ref [] in
  Array.iteri
    (fun index value ->
      if is_upper value then begin
        let previous = if index > 0 then Some array.(index - 1) else None in
        let next = if index + 1 < length then Some array.(index + 1) else None in
        let starts_word =
          match previous with
          | None -> false
          | Some previous when previous = underscore -> false
          | Some previous when not (is_upper previous) -> true
          | Some _ -> ( match next with Some next -> is_lowercase_letter next | None -> false)
        in
        if starts_word then output := underscore :: !output;
        output := Unicode.to_lowercase value :: !output
      end
      else output := value :: !output)
    array;
  join_snake (parts (List.rev !output))

(* `Http_client` becomes `HttpClient`. *)
let to_camel code_points =
  List.concat
    (List.mapi
       (fun index part ->
         match part with
         | first :: rest when index > 0 -> Unicode.to_uppercase first :: rest
         | part -> part)
       (parts code_points))

let correct_case code_points =
  let code_points = drop_underscores code_points in
  match code_points with
  | first :: _ when is_upper first ->
      if not (List.mem underscore code_points) then code_points
      else if not (List.exists is_lowercase_letter code_points) then
        join_snake (List.map (List.map Unicode.to_lowercase) (parts code_points))
      else to_camel code_points
  | _ -> to_snake code_points

let case_problem name code_points =
  let has_double_underscore =
    let rec loop = function
      | first :: (second :: _ as rest) -> (first = underscore && second = underscore) || loop rest
      | _ -> false
    in
    loop code_points
  in
  let message =
    match code_points with
    | first :: _ when first = underscore -> Some "Names cannot start with `_`."
    | first :: _ when is_upper first ->
        if not (List.mem underscore code_points) then None
        else if not (List.exists is_lowercase_letter code_points) then
          Some
            (Printf.sprintf
               "`%s` is written like a constant from another language. Constants are values, so \
                their names are lower_snake_case."
               name)
        else Some "A name that starts with an uppercase letter is UpperCamelCase, with no `_`."
    | _ ->
        if List.exists is_upper code_points then
          Some
            "A name that starts with a lowercase letter is lower_snake_case, with no uppercase \
             letters."
        else if List.nth code_points (List.length code_points - 1) = underscore then
          Some "Names cannot end with `_`."
        else if has_double_underscore then Some "`_` appears only singly, between the parts of a name."
        else None
  in
  Option.map (fun message -> ("lexer.name_case", message)) message

let describe value =
  Printf.sprintf "`%s` (U+%04X)" (Unicode.of_code_points [ value ]) value

(* The first problem with a name, checking in LEXER.md's order. *)
let problem name =
  let code_points = Unicode.code_points name in
  match case_problem name code_points with
  | Some problem -> Some problem
  | None when is_ascii name -> None
  | None ->
      if not (Unicode.is_nfc name) then
        Some
          ( "lexer.name_not_normalized",
            "This name is not in Unicode Normalization Form C, so the same-looking name could be \
             spelled another way." )
      else
        match List.find_opt (fun value -> not (Unicode.is_identifier_allowed value)) code_points with
        | Some (0x200C | 0x200D) ->
            (* Both are XID_Continue since Unicode 15.1, but not Allowed. *)
            Some
              ( "lexer.name_joiner",
                "The zero-width joiner and non-joiner are not supported in names yet." )
        | Some value ->
            Some
              ( "lexer.name_character_not_allowed",
                Printf.sprintf
                  "%s is not allowed in names. Names use only the characters Unicode recommends \
                   for identifiers (Identifier_Status=Allowed in UTS #39)."
                  (describe value) )
        | None when not (Unicode.is_moderately_restrictive name) ->
            Some
              ( "lexer.name_mixed_scripts",
                Printf.sprintf
                  "This name mixes the scripts %s. A name can mix Latin with at most one other \
                   script, and never Latin with Cyrillic or Greek."
                  (match List.rev (Unicode.script_names name) with
                  | last :: (_ :: _ as rest) -> String.concat ", " (List.rev rest) ^ " and " ^ last
                  | names -> String.concat ", " names) )
        | None -> None

let check name =
  match problem name with
  | None -> { kind = kind_of (Unicode.code_points name); name; problem = None; fix = None }
  | Some found ->
      let corrected =
        Unicode.of_code_points (correct_case (Unicode.code_points (Unicode.nfc name)))
      in
      let fix =
        match Unicode.code_points corrected with
        | first :: _
          when corrected <> name && Unicode.is_xid_start first && problem corrected = None
               && Token.word corrected = None ->
            Some corrected
        | _ -> None
      in
      let name = Option.value fix ~default:name in
      { kind = kind_of (Unicode.code_points name); name; problem = Some found; fix }

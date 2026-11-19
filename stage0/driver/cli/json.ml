type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | List of t list
  | Object of (string * t) list
  | Raw of string

let rec write buffer = function
  | Null -> Buffer.add_string buffer "null"
  | Bool value -> Buffer.add_string buffer (if value then "true" else "false")
  | Int value -> Buffer.add_string buffer (string_of_int value)
  | String value -> Buffer.add_string buffer (Diagnostic.encode_json_string value)
  | Raw text -> Buffer.add_string buffer text
  | List values ->
      Buffer.add_char buffer '[';
      List.iteri
        (fun index value ->
          if index > 0 then Buffer.add_char buffer ',';
          write buffer value)
        values;
      Buffer.add_char buffer ']'
  | Object fields ->
      Buffer.add_char buffer '{';
      List.iteri
        (fun index (name, value) ->
          if index > 0 then Buffer.add_char buffer ',';
          Buffer.add_string buffer (Diagnostic.encode_json_string name);
          Buffer.add_char buffer ':';
          write buffer value)
        fields;
      Buffer.add_char buffer '}'

let to_string value =
  let buffer = Buffer.create 1024 in
  write buffer value;
  Buffer.contents buffer

let encode_option encode = function Some value -> encode value | None -> Null

let make_document ~diagnostics fields =
  Object (("format", Int 1) :: ("diagnostics", List diagnostics) :: fields)

let print value = Output.print_line (to_string value)

exception Malformed

let parse text =
  let length = String.length text in
  let position = ref 0 in
  let peek () = if !position < length then Some text.[!position] else None in
  let advance () = incr position in
  let rec skip_space () =
    match peek () with
    | Some (' ' | '\t' | '\n' | '\r') ->
        advance ();
        skip_space ()
    | _ -> ()
  in
  let expect character = if peek () = Some character then advance () else raise Malformed in
  let parse_literal word value =
    let word_length = String.length word in
    if !position + word_length <= length && String.sub text !position word_length = word then begin
      position := !position + word_length;
      value
    end
    else raise Malformed
  in
  let parse_hex () =
    if !position + 4 > length then raise Malformed;
    let digits = String.sub text !position 4 in
    position := !position + 4;
    match int_of_string_opt ("0x" ^ digits) with Some code -> code | None -> raise Malformed
  in
  let parse_string () =
    expect '"';
    let buffer = Buffer.create 16 in
    let rec loop () =
      match peek () with
      | None -> raise Malformed
      | Some '"' -> advance ()
      | Some '\\' ->
          advance ();
          (match peek () with
          | Some '"' -> Buffer.add_char buffer '"'
          | Some '\\' -> Buffer.add_char buffer '\\'
          | Some '/' -> Buffer.add_char buffer '/'
          | Some 'b' -> Buffer.add_char buffer '\b'
          | Some 'f' -> Buffer.add_char buffer '\012'
          | Some 'n' -> Buffer.add_char buffer '\n'
          | Some 'r' -> Buffer.add_char buffer '\r'
          | Some 't' -> Buffer.add_char buffer '\t'
          | Some 'u' ->
              advance ();
              let high = parse_hex () in
              let code =
                if
                  high >= 0xD800 && high <= 0xDBFF
                  && !position + 1 < length
                  && text.[!position] = '\\'
                  && text.[!position + 1] = 'u'
                then begin
                  position := !position + 2;
                  let low = parse_hex () in
                  0x10000 + ((high - 0xD800) lsl 10) + (low - 0xDC00)
                end
                else high
              in
              let code = if Uchar.is_valid code then code else Uchar.to_int Uchar.rep in
              Buffer.add_utf_8_uchar buffer (Uchar.of_int code);
              position := !position - 1
          | _ -> raise Malformed);
          advance ();
          loop ()
      | Some character ->
          Buffer.add_char buffer character;
          advance ();
          loop ()
    in
    loop ();
    Buffer.contents buffer
  in
  let parse_number () =
    let start = !position in
    let rec loop () =
      match peek () with
      | Some ('0' .. '9' | '-' | '+' | '.' | 'e' | 'E') ->
          advance ();
          loop ()
      | _ -> ()
    in
    loop ();
    let written = String.sub text start (!position - start) in
    match int_of_string_opt written with
    | Some value -> Int value
    | None -> (
        match float_of_string_opt written with
        | Some value -> Int (int_of_float value)
        | None -> raise Malformed)
  in
  let rec parse_value () =
    skip_space ();
    match peek () with
    | Some '{' ->
        advance ();
        skip_space ();
        if peek () = Some '}' then begin
          advance ();
          Object []
        end
        else
          let rec parse_fields acc =
            skip_space ();
            let name = parse_string () in
            skip_space ();
            expect ':';
            let field = parse_value () in
            skip_space ();
            match peek () with
            | Some ',' ->
                advance ();
                parse_fields ((name, field) :: acc)
            | Some '}' ->
                advance ();
                Object (List.rev ((name, field) :: acc))
            | _ -> raise Malformed
          in
          parse_fields []
    | Some '[' ->
        advance ();
        skip_space ();
        if peek () = Some ']' then begin
          advance ();
          List []
        end
        else
          let rec parse_items acc =
            let item = parse_value () in
            skip_space ();
            match peek () with
            | Some ',' ->
                advance ();
                parse_items (item :: acc)
            | Some ']' ->
                advance ();
                List (List.rev (item :: acc))
            | _ -> raise Malformed
          in
          parse_items []
    | Some '"' -> String (parse_string ())
    | Some 't' -> parse_literal "true" (Bool true)
    | Some 'f' -> parse_literal "false" (Bool false)
    | Some 'n' -> parse_literal "null" Null
    | Some ('-' | '0' .. '9') -> parse_number ()
    | _ -> raise Malformed
  in
  let result = parse_value () in
  skip_space ();
  if !position <> length then raise Malformed;
  result

let lookup_field name = function
  | Object fields -> Option.value ~default:Null (List.assoc_opt name fields)
  | _ -> Null

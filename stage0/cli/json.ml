(* The JSON the commands write with --json. Strings are written as diagnostics
   write them, so the output is always valid UTF-8. *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | List of t list
  | Object of (string * t) list
  | Raw of string  (** JSON written elsewhere, such as a diagnostic's *)

let rec write buffer = function
  | Null -> Buffer.add_string buffer "null"
  | Bool value -> Buffer.add_string buffer (if value then "true" else "false")
  | Int value -> Buffer.add_string buffer (string_of_int value)
  | String value -> Buffer.add_string buffer (Diagnostic.json_string value)
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
          Buffer.add_string buffer (Diagnostic.json_string name);
          Buffer.add_char buffer ':';
          write buffer value)
        fields;
      Buffer.add_char buffer '}'

let to_string value =
  let buffer = Buffer.create 1024 in
  write buffer value;
  Buffer.contents buffer

let option f = function Some value -> f value | None -> Null

(* A command's document: the format version, its diagnostics, and its own
   fields. *)
let document ~diagnostics fields =
  Object (("format", Int 1) :: ("diagnostics", List diagnostics) :: fields)

let print value = Output.print_line (to_string value)

exception Malformed

(* A JSON text as a value. A number with a fraction or an exponent is cut
   to an integer, since the messages read here carry only integers. *)
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
  let expect c = if peek () = Some c then advance () else raise Malformed in
  let literal word value =
    let n = String.length word in
    if !position + n <= length && String.sub text !position n = word then begin
      position := !position + n;
      value
    end
    else raise Malformed
  in
  let hex () =
    if !position + 4 > length then raise Malformed;
    let digits = String.sub text !position 4 in
    position := !position + 4;
    match int_of_string_opt ("0x" ^ digits) with Some code -> code | None -> raise Malformed
  in
  let string_ () =
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
              let high = hex () in
              let code =
                if
                  high >= 0xD800 && high <= 0xDBFF
                  && !position + 1 < length
                  && text.[!position] = '\\'
                  && text.[!position + 1] = 'u'
                then begin
                  position := !position + 2;
                  let low = hex () in
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
      | Some c ->
          Buffer.add_char buffer c;
          advance ();
          loop ()
    in
    loop ();
    Buffer.contents buffer
  in
  let number () =
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
  let rec value () =
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
          let rec fields acc =
            skip_space ();
            let name = string_ () in
            skip_space ();
            expect ':';
            let field = value () in
            skip_space ();
            match peek () with
            | Some ',' ->
                advance ();
                fields ((name, field) :: acc)
            | Some '}' ->
                advance ();
                Object (List.rev ((name, field) :: acc))
            | _ -> raise Malformed
          in
          fields []
    | Some '[' ->
        advance ();
        skip_space ();
        if peek () = Some ']' then begin
          advance ();
          List []
        end
        else
          let rec items acc =
            let item = value () in
            skip_space ();
            match peek () with
            | Some ',' ->
                advance ();
                items (item :: acc)
            | Some ']' ->
                advance ();
                List (List.rev (item :: acc))
            | _ -> raise Malformed
          in
          items []
    | Some '"' -> String (string_ ())
    | Some 't' -> literal "true" (Bool true)
    | Some 'f' -> literal "false" (Bool false)
    | Some 'n' -> literal "null" Null
    | Some ('-' | '0' .. '9') -> number ()
    | _ -> raise Malformed
  in
  let result = value () in
  skip_space ();
  if !position <> length then raise Malformed;
  result

(* A field of an object, or [Null]. *)
let field name = function
  | Object fields -> Option.value ~default:Null (List.assoc_opt name fields)
  | _ -> Null

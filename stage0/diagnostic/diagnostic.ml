type span = Source.span = private { start : int; stop : int }

module Code = struct
  type t =
    | Invalid_utf8
    | Carriage_return
    | Forbidden_character
    | Comment
    | Semicolon
    | Unexpected_character
    | Strict_equality
    | Character_literal
    | Name_case
    | Name_not_normalized
    | Name_character_not_allowed
    | Name_joiner
    | Name_mixed_scripts
    | Number_suffix
    | Number_uppercase_prefix
    | Number_uppercase_exponent
    | Number_missing_digits
    | Number_invalid_digit
    | Number_followed_by_name
    | Number_underscore
    | Number_leading_zero
    | Unterminated_string
    | Invalid_escape
    | Line_break_in_interpolation
    | Empty_interpolation
    | Interpolation_too_deep
    | Raw_string_quotes
    | Raw_string_closing_not_alone
    | Raw_string_indentation
    | Unclosed_bracket
    | Unmatched_closing_bracket
    | Too_many_diagnostics

  let name code =
    "lexer."
    ^
    match code with
    | Invalid_utf8 -> "invalid_utf8"
    | Carriage_return -> "carriage_return"
    | Forbidden_character -> "forbidden_character"
    | Comment -> "comment"
    | Semicolon -> "semicolon"
    | Unexpected_character -> "unexpected_character"
    | Strict_equality -> "strict_equality"
    | Character_literal -> "character_literal"
    | Name_case -> "name_case"
    | Name_not_normalized -> "name_not_normalized"
    | Name_character_not_allowed -> "name_character_not_allowed"
    | Name_joiner -> "name_joiner"
    | Name_mixed_scripts -> "name_mixed_scripts"
    | Number_suffix -> "number_suffix"
    | Number_uppercase_prefix -> "number_uppercase_prefix"
    | Number_uppercase_exponent -> "number_uppercase_exponent"
    | Number_missing_digits -> "number_missing_digits"
    | Number_invalid_digit -> "number_invalid_digit"
    | Number_followed_by_name -> "number_followed_by_name"
    | Number_underscore -> "number_underscore"
    | Number_leading_zero -> "number_leading_zero"
    | Unterminated_string -> "unterminated_string"
    | Invalid_escape -> "invalid_escape"
    | Line_break_in_interpolation -> "line_break_in_interpolation"
    | Empty_interpolation -> "empty_interpolation"
    | Interpolation_too_deep -> "interpolation_too_deep"
    | Raw_string_quotes -> "raw_string_quotes"
    | Raw_string_closing_not_alone -> "raw_string_closing_not_alone"
    | Raw_string_indentation -> "raw_string_indentation"
    | Unclosed_bracket -> "unclosed_bracket"
    | Unmatched_closing_bracket -> "unmatched_closing_bracket"
    | Too_many_diagnostics -> "too_many_diagnostics"
end

type edit = { span : span; replacement : string }
type fix = { title : string; edits : edit list }

type t = {
  code : Code.t;
  message : string;
  span : span;
  notes : (span * string) list;
  fixes : fix list;
}

let make ?(notes = []) ?(fixes = []) ~code span message = { code; message; span; notes; fixes }
let fix title edits = { title; edits }
let replace span replacement = { span; replacement }
let insert offset replacement = { span = Source.zero_width offset; replacement }
let delete span = { span; replacement = "" }

let apply_fix text fix =
  let edits = List.sort (fun (a : edit) (b : edit) -> compare a.span.start b.span.start) fix.edits in
  let buffer = Buffer.create (String.length text) in
  let position =
    List.fold_left
      (fun position (edit : edit) ->
        if edit.span.start < position then invalid_arg "Diagnostic.apply_fix: overlapping edits";
        Buffer.add_substring buffer text position (edit.span.start - position);
        Buffer.add_string buffer edit.replacement;
        edit.span.stop)
      0 edits
  in
  Buffer.add_substring buffer text position (String.length text - position);
  Buffer.contents buffer

let limit = 200

module Collector = struct
  type diagnostic = t
  type nonrec t = diagnostic Dynarray.t
  type mark = int

  let create () = Dynarray.create ()
  let add collector diagnostic = Dynarray.add_last collector diagnostic
  let mark collector = Dynarray.length collector
  let reset collector mark = Dynarray.truncate collector mark

  let to_list collector =
    List.stable_sort
      (fun (a : diagnostic) (b : diagnostic) -> compare a.span.start b.span.start)
      (Dynarray.to_list collector)
end

let shown diagnostics =
  let rec take count = function
    | [] -> []
    | rest when count = limit ->
        let last = (List.nth diagnostics (limit - 1)).span.stop in
        [
          make ~code:Too_many_diagnostics (Source.zero_width last)
            (Printf.sprintf "%d more errors are not shown." (List.length rest));
        ]
    | first :: rest -> first :: take (count + 1) rest
  in
  take 0 diagnostics

(* Rendering *)

let location source offset =
  let line, column = Source.position source offset in
  Printf.sprintf "%s:%d:%d" (Source.path source) line column

(* A string in double quotes, with only quotes, backslashes, and control
   characters escaped, so that text in any script stays readable. *)
(* Calls [valid] with each valid UTF-8 sequence of [text] and [invalid] with
   each byte that does not start one. *)
let iter_utf8 text ~valid ~invalid =
  let rec loop index =
    if index < String.length text then begin
      let packed = Unicode.decode text index in
      if packed < 0 then begin
        invalid text.[index];
        loop (index + 1)
      end
      else begin
        let length = Unicode.decoded_length packed in
        valid (String.sub text index length);
        loop (index + length)
      end
    end
  in
  loop 0

let quote text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  iter_utf8 text
    ~valid:(fun character ->
      match character with
      | "\"" -> Buffer.add_string buffer "\\\""
      | "\\" -> Buffer.add_string buffer "\\\\"
      | "\n" -> Buffer.add_string buffer "\\n"
      | "\t" -> Buffer.add_string buffer "\\t"
      | c when String.length c = 1 && (Char.code c.[0] < 0x20 || Char.code c.[0] = 0x7F) ->
          Printf.bprintf buffer "\\x%02X" (Char.code c.[0])
      | c -> Buffer.add_string buffer c)
    ~invalid:(fun byte -> Printf.bprintf buffer "\\x%02X" (Char.code byte));
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let render source diagnostic =
  let buffer = Buffer.create 256 in
  let text = Source.text source in
  Printf.bprintf buffer "%s: error[%s]: %s\n" (location source diagnostic.span.start)
    (Code.name diagnostic.code) diagnostic.message;
  (* The line holding the start of the span, with the part of the span on that
     line marked. *)
  let start = diagnostic.span.start in
  let line_start =
    let line_start = Source.line_start source start in
    if line_start = 0 then Source.byte_order_mark_length source else line_start
  in
  let line_end = Source.line_end source start in
  let line = String.sub text line_start (line_end - line_start) in
  let _, start_column = Source.position source start in
  let _, stop_column = Source.position source (min diagnostic.span.stop line_end) in
  let is_printable =
    String.for_all (fun c -> c = '\t' || Char.code c >= 0x20) line
    &&
    let valid = ref true in
    iter_utf8 line ~valid:ignore ~invalid:(fun _ -> valid := false);
    !valid
  in
  if is_printable && String.length line <= 200 then begin
    Printf.bprintf buffer "  | %s\n" line;
    (* Keep tabs, so that the marker lines up under the span. *)
    let leading = Buffer.create 16 in
    for index = line_start to start - 1 do
      match text.[index] with
      | '\t' -> Buffer.add_char leading '\t'
      | c when Char.code c land 0xC0 = 0x80 -> ()
      | _ -> Buffer.add_char leading ' '
    done;
    Printf.bprintf buffer "  | %s%s\n" (Buffer.contents leading)
      (String.make (max 1 (stop_column - start_column)) '^')
  end;
  List.iter
    (fun (span, note) -> Printf.bprintf buffer "  note: %s: %s\n" (location source span.start) note)
    diagnostic.notes;
  List.iter
    (fun fix ->
      Printf.bprintf buffer "  fix: %s\n" fix.title;
      List.iter
        (fun (edit : edit) ->
          let original = String.sub text edit.span.start (edit.span.stop - edit.span.start) in
          Printf.bprintf buffer "    %s at %s\n"
            (if edit.span.start = edit.span.stop then "insert " ^ quote edit.replacement
             else if edit.replacement = "" then "delete " ^ quote original
             else Printf.sprintf "replace %s with %s" (quote original) (quote edit.replacement))
            (location source edit.span.start))
        fix.edits)
    diagnostic.fixes;
  Buffer.contents buffer

let json_string value =
  let buffer = Buffer.create (String.length value + 2) in
  Buffer.add_char buffer '"';
  iter_utf8 value
    ~valid:(fun character ->
      match character with
      | "\"" -> Buffer.add_string buffer "\\\""
      | "\\" -> Buffer.add_string buffer "\\\\"
      | "\n" -> Buffer.add_string buffer "\\n"
      | "\r" -> Buffer.add_string buffer "\\r"
      | "\t" -> Buffer.add_string buffer "\\t"
      | c when String.length c = 1 && (Char.code c.[0] < 0x20 || Char.code c.[0] = 0x7F) ->
          Printf.bprintf buffer "\\u%04x" (Char.code c.[0])
      | c -> Buffer.add_string buffer c)
    ~invalid:(fun _ -> Buffer.add_string buffer "\xEF\xBF\xBD");
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let json_span source span =
  let line, column = Source.position source span.start in
  let end_line, end_column = Source.position source span.stop in
  Printf.sprintf
    {|{"start":%d,"stop":%d,"line":%d,"column":%d,"end_line":%d,"end_column":%d}|}
    span.start span.stop line column end_line end_column

let to_json source diagnostics =
  let path = json_string (Source.path source) in
  let one diagnostic =
    let notes =
      List.map
        (fun (span, message) ->
          Printf.sprintf {|{"span":%s,"message":%s}|} (json_span source span) (json_string message))
        diagnostic.notes
    in
    let fixes =
      List.map
        (fun fix ->
          let edits =
            List.map
              (fun (edit : edit) ->
                Printf.sprintf {|{"start":%d,"stop":%d,"replacement":%s}|} edit.span.start
                  edit.span.stop (json_string edit.replacement))
              fix.edits
          in
          Printf.sprintf {|{"title":%s,"edits":[%s]}|} (json_string fix.title)
            (String.concat "," edits))
        diagnostic.fixes
    in
    Printf.sprintf {|{"path":%s,"code":%s,"message":%s,"span":%s,"notes":[%s],"fixes":[%s]}|} path
      (json_string (Code.name diagnostic.code)) (json_string diagnostic.message)
      (json_span source diagnostic.span) (String.concat "," notes) (String.concat "," fixes)
  in
  "[" ^ String.concat ",\n" (List.map one diagnostics) ^ "]\n"

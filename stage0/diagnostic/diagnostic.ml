type span = Source.span = { start : int; stop : int }
type edit = { span : span; replacement : string }
type fix = { title : string; edits : edit list }

type t = {
  code : string;
  message : string;
  span : span;
  notes : (span * string) list;
  fixes : fix list;
}

let make ?(notes = []) ?(fixes = []) ~code span message = { code; message; span; notes; fixes }
let fix title edits = { title; edits }
let replace span replacement = { span; replacement }
let insert offset replacement = { span = { start = offset; stop = offset }; replacement }
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
  type nonrec t = { kept : diagnostic Dynarray.t; mutable dropped : int }
  type mark = { kept_length : int; dropped_count : int }

  let create () = { kept = Dynarray.create (); dropped = 0 }

  let add collector diagnostic =
    if Dynarray.length collector.kept < limit then Dynarray.add_last collector.kept diagnostic
    else collector.dropped <- collector.dropped + 1

  let mark collector =
    { kept_length = Dynarray.length collector.kept; dropped_count = collector.dropped }

  let reset collector mark =
    Dynarray.truncate collector.kept mark.kept_length;
    collector.dropped <- mark.dropped_count

  let count collector = Dynarray.length collector.kept + collector.dropped

  let to_list collector =
    let sorted =
      List.stable_sort
        (fun (a : diagnostic) (b : diagnostic) -> compare a.span.start b.span.start)
        (Dynarray.to_list collector.kept)
    in
    if collector.dropped = 0 then sorted
    else
      let last = match List.rev sorted with last :: _ -> last.span | [] -> { start = 0; stop = 0 } in
      sorted
      @ [
          make ~code:"too_many_diagnostics" { start = last.stop; stop = last.stop }
            (Printf.sprintf "%d more errors are not shown." collector.dropped);
        ]
end

(* Rendering *)

let location source offset =
  let line, column = Source.position source offset in
  Printf.sprintf "%s:%d:%d" (Source.path source) line column

(* A string in double quotes, with only quotes, backslashes, and control
   characters escaped, so that text in any script stays readable. *)
let quote text =
  let buffer = Buffer.create (String.length text + 2) in
  Buffer.add_char buffer '"';
  String.iter
    (fun character ->
      match character with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c when Char.code c < 0x20 || Char.code c = 0x7F -> Printf.bprintf buffer "\\x%02X" (Char.code c)
      | c -> Buffer.add_char buffer c)
    text;
  Buffer.add_char buffer '"';
  Buffer.contents buffer

let render source diagnostic =
  let buffer = Buffer.create 256 in
  let text = Source.text source in
  Printf.bprintf buffer "%s: error[%s]: %s\n" (location source diagnostic.span.start)
    diagnostic.code diagnostic.message;
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
  let is_printable = String.for_all (fun c -> c = '\t' || Char.code c >= 0x20) line in
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
  String.iter
    (fun character ->
      match character with
      | '"' -> Buffer.add_string buffer "\\\""
      | '\\' -> Buffer.add_string buffer "\\\\"
      | '\n' -> Buffer.add_string buffer "\\n"
      | '\r' -> Buffer.add_string buffer "\\r"
      | '\t' -> Buffer.add_string buffer "\\t"
      | c when Char.code c < 0x20 || Char.code c = 0x7F ->
          Printf.bprintf buffer "\\u%04x" (Char.code c)
      | c -> Buffer.add_char buffer c)
    value;
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
      (json_string diagnostic.code) (json_string diagnostic.message)
      (json_span source diagnostic.span) (String.concat "," notes) (String.concat "," fixes)
  in
  "[" ^ String.concat ",\n" (List.map one diagnostics) ^ "]\n"

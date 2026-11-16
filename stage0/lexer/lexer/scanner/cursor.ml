type ending = Closed | Unterminated

type token = {
  kind : Token.kind;
  start : int;
  stop : int;
  ending : ending;
  first_line_break : Source.span option;
  blank_line : bool;
}

type item = Token of token | Line_end | End

type t = {
  source : Source.t;
  text : string;
  length : int;
  diagnostics : Diagnostic.Collector.t;
  mutable position : int;
  mutable first_line_break : Source.span option;
  mutable blank_line : bool;
  mutable line_is_blank : bool;
  mutable unterminated_at_end : bool;
  names : (string, Names.checked) Hashtbl.t;
  mutable previous : token option;
  mutable held : item list;
  mutable semicolons : int list;
  foreign_escape : t -> Buffer.t -> bool;
}

let create ~foreign_escape source diagnostics =
  {
    source;
    text = Source.text source;
    length = String.length (Source.text source);
    diagnostics;
    position = Source.line_start source 0;
    first_line_break = None;
    blank_line = false;
    line_is_blank = true;
    unterminated_at_end = false;
    names = Hashtbl.create 256;
    previous = None;
    held = [];
    semicolons = [];
    foreign_escape;
  }

let span = Source.span
let at_end cursor index = index >= cursor.length
let char cursor index = cursor.text.[index]
let is_at cursor index character = index < cursor.length && cursor.text.[index] = character
let satisfies cursor index predicate = index < cursor.length && predicate cursor.text.[index]

let report cursor ?notes ?fixes ~code span message =
  Diagnostic.Collector.add cursor.diagnostics
    (Diagnostic.make ?notes ?fixes ~code:(Lexer code) span message)

let is_line_break character = character = '\n' || character = '\r'
let is_end_of_line cursor index = at_end cursor index || is_line_break cursor.text.[index]
let is_space character = character = ' ' || character = '\t'
let is_digit character = character >= '0' && character <= '9'

let is_hexadecimal_digit character =
  is_digit character
  || (character >= 'a' && character <= 'f')
  || (character >= 'A' && character <= 'F')

let is_ascii_letter character =
  (character >= 'a' && character <= 'z') || (character >= 'A' && character <= 'Z')

let is_ascii_name_byte character =
  is_ascii_letter character || is_digit character || character = '_'

let is_ascii character = Char.code character < 0x80
let decode cursor index = Unicode.decode cursor.text index

let written_before cursor index =
  let rec character_start position =
    if position > 0 && Char.code cursor.text.[position] land 0xC0 = 0x80 then
      character_start (position - 1)
    else position
  in
  if index <= 0 then ""
  else
    let start = character_start (index - 1) in
    match Confusable_characters.find (Unicode.Decoded.code_point (decode cursor start)) with
    | Some (Spelled spelling) -> spelling
    | Some Space -> " "
    | Some (Opening_quote _) | None -> String.sub cursor.text start (index - start)

let without_joining_fixes cursor (span : Source.span) fixes =
  let text = String.sub cursor.text span.start (span.stop - span.start) in
  let before = written_before cursor span.start
  and after = String.sub cursor.text span.stop (min 2 (cursor.length - span.stop)) in
  List.filter
    (fun (fix : Source.span Diagnostic.fix) ->
      let written =
        Diagnostic.apply_edits text
          (List.map
             (fun (edit : Source.span Diagnostic.edit) ->
               {
                 edit with
                 span = Source.span (edit.span.start - span.start) (edit.span.stop - span.start);
               })
             fix.edits)
      in
      not (Token.joins_neighbor ~before ~after written))
    fixes

let code_fixes cursor span codes =
  without_joining_fixes cursor span
    (List.map
       (fun code -> Diagnostic.fix ("Write `" ^ code ^ "`") [ Diagnostic.replace span code ])
       codes)

let run_length cursor index character =
  let rec loop position =
    if is_at cursor position character then loop (position + 1) else position
  in
  loop index - index

let skip_spaces cursor index =
  let rec loop position =
    if satisfies cursor position is_space then loop (position + 1) else position
  in
  loop index

let end_of_line cursor index =
  let rec loop position =
    if is_end_of_line cursor position then position else loop (position + 1)
  in
  loop index

let line_break_length cursor index =
  if is_at cursor index '\r' && is_at cursor (index + 1) '\n' then 2 else 1

let indentation cursor offset =
  let start = Source.line_start cursor.source offset in
  String.sub cursor.text start (skip_spaces cursor start - start)

let spaces_before cursor offset =
  let line_start = Source.line_start cursor.source offset in
  let rec loop position =
    if position > line_start && is_space cursor.text.[position - 1] then loop (position - 1)
    else position
  in
  loop offset

let only_spaces_before cursor offset =
  spaces_before cursor offset = Source.line_start cursor.source offset

let describe_code_point value =
  match Unicode.forbidden_name value with
  | Some name -> Printf.sprintf "U+%04X %s" value name
  | None -> Printf.sprintf "U+%04X" value

let show_character cursor index =
  let decoded = decode cursor index in
  if not (Unicode.Decoded.is_valid decoded) then
    Printf.sprintf "the byte 0x%02X" (Char.code cursor.text.[index])
  else
    let value = Unicode.Decoded.code_point decoded in
    if value < 0x80 then Printf.sprintf "`%c`" (Char.chr value)
    else
      Printf.sprintf "`%s` (U+%04X)"
        (String.sub cursor.text index (Unicode.Decoded.length decoded))
        value

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

let is_at_end cursor index = index >= cursor.length
let lookup_char cursor index = cursor.text.[index]
let is_at cursor index character = index < cursor.length && cursor.text.[index] = character
let satisfies cursor index predicate = index < cursor.length && predicate cursor.text.[index]

let report cursor ?notes ?fixes ~code span message =
  Diagnostic.Collector.add cursor.diagnostics
    (Diagnostic.make ?notes ?fixes ~code:(Lexer code) span message)

let is_line_break character = character = '\n' || character = '\r'
let is_end_of_line cursor index = is_at_end cursor index || is_line_break cursor.text.[index]
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

let joins_neighbor cursor (span : Source.span) code =
  let before = if span.start > 0 then Some cursor.text.[span.start - 1] else None
  and after = if span.stop < cursor.length then Some cursor.text.[span.stop] else None in
  Token.joins_neighbor ~before ~after code

let list_code_fixes cursor span codes =
  List.filter_map
    (fun code ->
      if joins_neighbor cursor span code then None
      else Some (Diagnostic.fix ("Write `" ^ code ^ "`") [ Diagnostic.replace span code ]))
    codes

let decode cursor index = Unicode.decode cursor.text index

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

let compute_end_of_line cursor index =
  let rec loop position =
    if is_end_of_line cursor position then position else loop (position + 1)
  in
  loop index

let measure_line_break cursor index =
  if is_at cursor index '\r' && is_at cursor (index + 1) '\n' then 2 else 1

let extract_indentation cursor offset =
  let start = Source.line_start cursor.source offset in
  String.sub cursor.text start (skip_spaces cursor start - start)

let count_spaces_before cursor offset =
  let line_start = Source.line_start cursor.source offset in
  let rec loop position =
    if position > line_start && is_space cursor.text.[position - 1] then loop (position - 1)
    else position
  in
  loop offset

let has_only_spaces_before cursor offset =
  count_spaces_before cursor offset = Source.line_start cursor.source offset

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

(* The scanner's state: an index moving over the file's bytes, the trivia
   seen since the last token, and the diagnostics. *)

type t = {
  source : Source.t;
  text : string;
  length : int;
  diagnostics : Diagnostic.Collector.t;
  mutable position : int;
  (* Trivia since the last token. *)
  mutable first_line_break : Source.span option;
  mutable blank_line : bool;
  mutable line_is_blank : bool;
  (* Set by a token that ends at the start of a line, as an unterminated raw
     string can: the line break before that point, which comes before the
     next token. *)
  mutable line_break_after_token : Source.span option;
  (* Each name spelling is checked once per file, and its tokens share one
     string. *)
  names : (string, Names.checked) Hashtbl.t;
}

let create source diagnostics =
  {
    source;
    text = Source.text source;
    length = String.length (Source.text source);
    diagnostics;
    position = Source.byte_order_mark_length source;
    first_line_break = None;
    blank_line = false;
    line_is_blank = true;
    line_break_after_token = None;
    names = Hashtbl.create 256;
  }

(* How a construct that must end on its line ended. [Cut_off] means it
   stopped at the end of its line because of an error already reported, and
   every enclosing construct that must end on its line ends there too,
   without another error. The cursor is then always at a line break or the
   end of the file. *)
type ending = Closed | Cut_off

(* What the scanner found next. It always stops at a line break, which the
   caller treats as trivia or as an error. *)
type item =
  | Token of { kind : Token.kind; start : int; ending : ending }
  | Line_end
  | End

let span = Source.span

(* The byte at [index], or -1 past the end. *)
let byte cursor index =
  if index < cursor.length then Char.code (String.unsafe_get cursor.text index) else -1

let report cursor ?notes ?fixes ~code span message =
  Diagnostic.Collector.add cursor.diagnostics (Diagnostic.make ?notes ?fixes ~code span message)

let is_line_break byte = byte = 0x0A || byte = 0x0D
let is_end_of_line byte = byte < 0 || is_line_break byte
let is_space byte = byte = 0x20 || byte = 0x09
let is_digit byte = byte >= 0x30 && byte <= 0x39
let is_ascii_letter byte = (byte >= 0x61 && byte <= 0x7A) || (byte >= 0x41 && byte <= 0x5A)
let is_ascii_name_byte byte = is_ascii_letter byte || is_digit byte || byte = 0x5F
let quote = Char.code '"'
let dollar = Char.code '$'

(* The decoded character at [index]: [(code_point lsl 3) lor length], or -1
   for invalid UTF-8 or the end of the file. *)
let decode cursor index = if index < cursor.length then Unicode.decode cursor.text index else -1

let run_length cursor index character =
  let rec loop position = if byte cursor position = character then loop (position + 1) else position in
  loop index - index

let skip_spaces cursor index =
  let rec loop position = if is_space (byte cursor position) then loop (position + 1) else position in
  loop index

let end_of_line cursor index =
  let rec loop position = if is_end_of_line (byte cursor position) then position else loop (position + 1) in
  loop index

(* The length of the line break at [index]: 2 for a carriage return and line
   feed, 1 for either alone. *)
let line_break_length cursor index =
  if byte cursor index = 0x0D && byte cursor (index + 1) = 0x0A then 2 else 1

let indentation cursor offset =
  let start = Source.line_start cursor.source offset in
  String.sub cursor.text start (skip_spaces cursor start - start)

(* Where the whitespace before [offset] on its line starts. *)
let spaces_before cursor offset =
  let line_start = Source.line_start cursor.source offset in
  let rec loop position =
    if position > line_start && is_space (byte cursor (position - 1)) then loop (position - 1)
    else position
  in
  loop offset

let only_spaces_before cursor offset =
  spaces_before cursor offset
  = max (Source.line_start cursor.source offset) (Source.byte_order_mark_length cursor.source)

(* Describing characters in messages, without copying bytes that are not
   valid UTF-8 into them. *)

let describe_code_point value =
  match Unicode.forbidden_name value with
  | Some name -> Printf.sprintf "U+%04X %s" value name
  | None -> Printf.sprintf "U+%04X" value

let show_character cursor index =
  let packed = decode cursor index in
  if packed < 0 then Printf.sprintf "the byte 0x%02X" (byte cursor index)
  else
    let value = Unicode.decoded_code_point packed in
    if value < 0x80 then Printf.sprintf "`%c`" (Char.chr value)
    else Printf.sprintf "`%s` (U+%04X)" (String.sub cursor.text index (Unicode.decoded_length packed)) value

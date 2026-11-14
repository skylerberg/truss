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
  (* Whether the file ends inside an unterminated comment or multi-line raw
     string, an error already reported. *)
  mutable unterminated_at_end : bool;
  (* Each name spelling is checked once per file, and its tokens share one
     string. *)
  names : (string, Names.checked) Hashtbl.t;
  (* The kind of the last token scanned in this file or interpolation, which
     decides what a `.` or a `...` after it means. *)
  mutable previous : Token.kind option;
  (* Whether this cursor only scans ahead for the kind of the next token. A
     cursor that scans ahead does not scan further ahead itself, so that
     each token is scanned at most twice. *)
  is_peek : bool;
}

let create source diagnostics =
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
    is_peek = false;
  }

(* A copy of [cursor] at [index] for scanning ahead: what it scans changes
   nothing in [cursor], and what it reports is discarded. *)
let peek cursor index =
  {
    cursor with
    position = index;
    diagnostics = Diagnostic.Collector.create ();
    previous = None;
    is_peek = true;
  }

(* How a construct that must end on its line ended. [Unterminated] means
   that it has no closing delimiter on its line, an error already reported,
   as for a string with no closing quote. Every enclosing construct that
   must end on its line is then unterminated too, with no further error.
   The cursor is then always at a line break or the end of the file. *)
type ending = Closed | Unterminated

(* The next thing in the input. The scanner always stops at a line break,
   which the caller treats as trivia or as an error. *)
type item = Token of { kind : Token.kind; start : int; ending : ending } | Line_end | End

let span = Source.span

(* The byte at [index], or -1 past the end. *)
let byte cursor index =
  if index < cursor.length then Char.code (String.unsafe_get cursor.text index) else -1

let report cursor ?notes ?fixes ~code span message =
  Diagnostic.Collector.add cursor.diagnostics
    (Diagnostic.make ?notes ?fixes ~code:(Lexer code) span message)

let is_line_break byte = byte = 0x0A || byte = 0x0D
let is_end_of_line byte = byte < 0 || is_line_break byte
let is_space byte = byte = 0x20 || byte = 0x09
let is_digit byte = byte >= 0x30 && byte <= 0x39

let is_hexadecimal_digit byte =
  is_digit byte || (byte >= 0x61 && byte <= 0x66) || (byte >= 0x41 && byte <= 0x46)

let is_ascii_letter byte = (byte >= 0x61 && byte <= 0x7A) || (byte >= 0x41 && byte <= 0x5A)
let is_ascii_name_byte byte = is_ascii_letter byte || is_digit byte || byte = 0x5F
let quote = Char.code '"'
let dollar = Char.code '$'

(* The decoded character at [index]: [(code_point lsl 3) lor length], or -1
   for invalid UTF-8 or the end of the file. *)
let decode cursor index = if index < cursor.length then Unicode.decode cursor.text index else -1

let run_length cursor index character =
  let rec loop position =
    if byte cursor position = character then loop (position + 1) else position
  in
  loop index - index

let skip_spaces cursor index =
  let rec loop position =
    if is_space (byte cursor position) then loop (position + 1) else position
  in
  loop index

let end_of_line cursor index =
  let rec loop position =
    if is_end_of_line (byte cursor position) then position else loop (position + 1)
  in
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
  spaces_before cursor offset = Source.line_start cursor.source offset

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
    else
      Printf.sprintf "`%s` (U+%04X)"
        (String.sub cursor.text index (Unicode.decoded_length packed))
        value

(* The edit that writes [code], one or more tokens, in place of [span]. A
   space goes between [code] and a neighbor that would otherwise join it
   into another token: `fn.5` is fixed to `fn 0.5`, not to the name `fn0`
   and `.5`, and `<>=` to `!= =`, not to `!==`. A name byte followed by a
   quote joins too, as a string's tag or prefix. With no [code], the edit
   deletes [span], and leaves a space if its two neighbors would join. *)
let replace_code cursor (span : Source.span) code =
  let is_name_byte byte = is_ascii_name_byte byte || byte >= 0x80 in
  let is_operator_byte byte =
    byte >= 0 && byte < 0x80 && String.contains "!%&*+-./:<=>^|" (Char.chr byte)
  in
  let joins left right =
    (is_name_byte left && (is_name_byte right || right = quote))
    || (is_operator_byte left && is_operator_byte right)
  in
  if code = "" then
    Diagnostic.replace span
      (if span.start > 0 && joins (byte cursor (span.start - 1)) (byte cursor span.stop) then " "
       else "")
  else
    let before =
      if span.start > 0 && joins (byte cursor (span.start - 1)) (Char.code code.[0]) then " "
      else ""
    and after =
      if joins (Char.code code.[String.length code - 1]) (byte cursor span.stop) then " " else ""
    in
    Diagnostic.replace span (before ^ code ^ after)

(* String literals: ordinary strings with escapes, raw strings on one line
   or several, interpolations, and character literals from other languages.

   An interpolation holds tokens, so these functions take [scan], the
   scanner's function for the next item, as an argument. Every function for
   a construct that must end on its line returns how it ended. When one
   returns [Unterminated], its caller ends at the same position. *)

open Token
open Cursor

(* Interpolations may nest at most this deep. *)
let maximum_nesting = 32

type scan = Cursor.t -> inline:bool -> nesting:int -> Cursor.item

(* A string's texts and interpolations as they are scanned. A text is
   completed only when an interpolation starts or the string ends, so the
   result always alternates, starting and ending with a text. *)
type builder = {
  buffer : Buffer.t;
  mutable text_start : int;
  mutable pairs : (text * interpolation) list;
}

let builder start = { buffer = Buffer.create 32; text_start = start; pairs = [] }

let take_text builder stop =
  let text = { value = Buffer.contents builder.buffer; span = span builder.text_start stop } in
  Buffer.clear builder.buffer;
  text

let add_interpolation builder (interpolation : interpolation) =
  let text = take_text builder interpolation.span.start in
  builder.pairs <- (text, interpolation) :: builder.pairs;
  builder.text_start <- interpolation.span.stop

let finish builder stop =
  let last = take_text builder stop in
  match List.rev builder.pairs with
  | [] -> (last, [||])
  | (first, _) :: rest_pairs as pairs ->
      let following = List.map fst rest_pairs @ [ last ] in
      ( first,
        Array.of_list
          (List.map2 (fun (_, interpolation) text -> (interpolation, text)) pairs following) )

let literal ~tag ~form builder stop =
  let first, rest = finish builder stop in
  String { tag; form; first; rest }

let ordinary_special byte = byte = quote || byte = Char.code '\\' || byte = dollar
let raw_special byte = byte = quote || byte = dollar

let next kind start stop ~ending =
  Layout.Next
    {
      kind;
      span = span start stop;
      first_line_break = None;
      blank_line = false;
      unterminated_string = ending = Unterminated;
    }

(* An interpolation, at its delimiter: `${`, or the `$`s and `{` of a raw
   string opened with `$`s. *)
let rec scan_interpolation cursor ~scan ~nesting ~delimiter_length =
  let start = cursor.position in
  if nesting + 1 > maximum_nesting then begin
    report cursor ~code:Interpolation_too_deep
      (span start (start + delimiter_length))
      (Printf.sprintf "Interpolations can nest at most %d deep." maximum_nesting);
    cursor.position <- end_of_line cursor start;
    let end_of_input = Source.zero_width cursor.position in
    ( {
        tokens =
          [|
            {
              kind = End_of_file;
              span = end_of_input;
              line_break_before = false;
              blank_line_before = false;
            };
          |];
        span = span start cursor.position;
      },
      Unterminated )
  end
  else begin
    cursor.position <- start + delimiter_length;
    let braces = ref 0 and count = ref 0 in
    let finished = ref false and closed = ref false and ending = ref Closed in
    let end_of_input position =
      Layout.End
        {
          position;
          first_line_break = None;
          blank_line = false;
          ends_unterminated = !ending = Unterminated;
        }
    in
    let next_input () =
      if !finished then end_of_input cursor.position
      else
        match scan cursor ~inline:true ~nesting:(nesting + 1) with
        | Line_end | End ->
            report cursor ~code:Line_break_in_interpolation (span start cursor.position)
              "An interpolation cannot contain a line break. Move the expression into a `let` \
               before the string.";
            finished := true;
            ending := Unterminated;
            end_of_input cursor.position
        | Token { kind = Punctuation (Close Curly); start = brace; _ } when !braces = 0 ->
            finished := true;
            closed := true;
            end_of_input brace
        | Token { kind; start = token_start; ending = token_ending } ->
            (match kind with
            | Punctuation (Open Curly) -> incr braces
            | Punctuation (Close Curly) -> decr braces
            | _ -> ());
            incr count;
            if token_ending = Unterminated then begin
              finished := true;
              ending := Unterminated
            end;
            next kind token_start cursor.position ~ending:token_ending
    in
    let tokens =
      Layout.interpolation ~source:cursor.source ~diagnostics:cursor.diagnostics next_input
    in
    let interpolation_span = span start cursor.position in
    if !closed && !count = 0 then
      report cursor ~code:Empty_interpolation
        ~fixes:
          [
            Diagnostic.fix "Remove the empty interpolation" [ Diagnostic.delete interpolation_span ];
          ]
        interpolation_span "An interpolation needs an expression.";
    ({ tokens; span = interpolation_span }, !ending)
  end

(* At a run of quotes, or of dollar signs before a raw string. *)
and scan_string cursor ~scan ~tag ~nesting =
  let start = cursor.position in
  let dollars = run_length cursor start dollar in
  let quotes = run_length cursor (start + dollars) quote in
  if dollars = 0 && quotes = 1 then scan_ordinary cursor ~scan ~tag ~nesting
  else if dollars = 0 && quotes = 2 then begin
    cursor.position <- start + 2;
    ( String
        {
          tag;
          form = Ordinary;
          first = { value = ""; span = span (start + 1) (start + 1) };
          rest = [||];
        },
      Closed )
  end
  else scan_raw cursor ~scan ~tag ~nesting ~dollars ~quotes

(* [closing] is the byte that closes the string: a quote, or the delimiter
   of another language's string that is scanned as an ordinary string. *)
and scan_ordinary ?(closing = quote) cursor ~scan ~tag ~nesting =
  let open_quote = cursor.position in
  let literal_start =
    match tag with Some (_, (tag_span : span)) -> tag_span.start | None -> open_quote
  in
  cursor.position <- open_quote + 1;
  let builder = builder cursor.position in
  (* Returns how the string ended and where its last text stops. *)
  let rec loop () =
    Source_text.copy_plain cursor builder.buffer ~special:(fun byte ->
        ordinary_special byte || byte = closing);
    let position = cursor.position in
    let current = byte cursor position in
    if is_end_of_line current then begin
      let message =
        "This string is not closed on its line. An ordinary string fits on one line; text that \
         spans lines goes in a raw string, between `\"\"\"`s."
      in
      if nesting = 0 then begin
        report cursor ~code:Unterminated_string
          ~fixes:[ Diagnostic.fix "Close the string" [ Diagnostic.insert position "\"" ] ]
          (span literal_start position) message;
        (Unterminated, position)
      end
      else begin
        report cursor ~code:Unterminated_string (span literal_start position) message;
        (Unterminated, position)
      end
    end
    else if current = closing then begin
      cursor.position <- position + 1;
      (Closed, position)
    end
    else if current = Char.code '\\' then
      match scan_escape cursor builder.buffer with
      | `Continue -> loop ()
      | `End_of_line -> (Unterminated, cursor.position)
    else if current = dollar && byte cursor (position + 1) = Char.code '{' then begin
      let interpolation, ending = scan_interpolation cursor ~scan ~nesting ~delimiter_length:2 in
      add_interpolation builder interpolation;
      match ending with Closed -> loop () | Unterminated -> (Unterminated, cursor.position)
    end
    else if current = dollar then begin
      Buffer.add_char builder.buffer '$';
      cursor.position <- position + 1;
      loop ()
    end
    else begin
      Source_text.read_character cursor builder.buffer ~context:Ordinary_string;
      loop ()
    end
  in
  let ending, stop = loop () in
  (literal ~tag ~form:Ordinary builder stop, ending)

(* An escape in an ordinary string, at its `\`. A `\` at the end of a line
   ends the string there. *)
and scan_escape cursor buffer =
  let start = cursor.position in
  let escaped = byte cursor (start + 1) in
  let simple value =
    Buffer.add_char buffer value;
    cursor.position <- start + 2;
    `Continue
  in
  let problem stop message =
    report cursor ~code:Invalid_escape (span start stop) message;
    cursor.position <- stop;
    `Continue
  in
  (* The value of exactly [count] hexadecimal digits at [position]. *)
  let hex_value position count =
    let rec all index =
      index >= count || (is_hexadecimal_digit (byte cursor (position + index)) && all (index + 1))
    in
    if all 0 then Some (int_of_string ("0x" ^ String.sub cursor.text position count)) else None
  in
  let is_scalar value = value <= 0x10FFFF && not (value >= 0xD800 && value <= 0xDFFF) in
  (* An escape of another language, ending at [stop], for the character
     [value]: its fix writes the code point, and the string has the
     character. *)
  let foreign_escape stop value =
    let replacement = Printf.sprintf "\\u{%X}" value in
    report cursor ~code:Invalid_escape
      ~fixes:
        [
          Diagnostic.fix
            ("Write `" ^ replacement ^ "`")
            [ Diagnostic.replace (span start stop) replacement ];
        ]
      (span start stop)
      (Printf.sprintf
         "`%s` is not an escape in Truss. A character is written by its code point: `%s`."
         (String.sub cursor.text start (stop - start))
         replacement);
    Unicode.encode buffer value;
    cursor.position <- stop;
    `Continue
  in
  let unknown () =
    let packed = decode cursor (start + 1) in
    let length = if packed < 0 then 1 else Unicode.decoded_length packed in
    let written =
      if packed < 0 then Printf.sprintf "`\\` followed by %s" (show_character cursor (start + 1))
      else Printf.sprintf "`%s`" (String.sub cursor.text start (1 + length))
    in
    problem
      (start + 1 + length)
      (Printf.sprintf
         "%s is not an escape. The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, `\\\"`, `\\${`, \
          and `\\u{...}`. For text with backslashes, such as a regular expression or a Windows \
          path, a raw string has no escapes: `\"\"\"\\d+\"\"\"`."
         written)
  in
  if is_end_of_line escaped then begin
    report cursor ~code:Invalid_escape
      (span start (start + 1))
      "A `\\` at the end of a line does not continue the string. Text that spans lines goes in a \
       raw string, between `\"\"\"`s.";
    cursor.position <- start + 1;
    `End_of_line
  end
  else
    match Char.chr escaped with
    | 'n' -> simple '\n'
    | 't' -> simple '\t'
    | 'r' -> simple '\r'
    | '0' -> simple '\000'
    | '\\' -> simple '\\'
    | '"' -> simple '"'
    | '$' when byte cursor (start + 2) = Char.code '{' ->
        Buffer.add_string buffer "${";
        cursor.position <- start + 3;
        `Continue
    | 'u' ->
        let form = "A Unicode escape is written `\\u{...}`, with 1 to 6 hexadecimal digits." in
        if byte cursor (start + 2) <> Char.code '{' then
          match hex_value (start + 2) 4 with
          | Some value when is_scalar value -> foreign_escape (start + 6) value
          | _ -> problem (start + 2) form
        else
          let digits_start = start + 3 in
          let rec digits_end position =
            if is_hexadecimal_digit (byte cursor position) then digits_end (position + 1)
            else position
          in
          let stop = digits_end digits_start in
          let count = stop - digits_start in
          if byte cursor stop <> Char.code '}' then problem stop form
          else if count = 0 || count > 6 then problem (stop + 1) form
          else
            let digits = String.sub cursor.text digits_start count in
            let value = int_of_string ("0x" ^ digits) in
            if value > 0x10FFFF || (value >= 0xD800 && value <= 0xDFFF) then
              problem (stop + 1)
                (Printf.sprintf
                   "`\\u{%s}` is not a Unicode scalar value: surrogates and values above 10FFFF \
                    have no character."
                   digits)
            else begin
              Unicode.encode buffer value;
              cursor.position <- stop + 1;
              `Continue
            end
    | 'x' -> (
        match hex_value (start + 2) 2 with
        | Some value -> foreign_escape (start + 4) value
        | None -> unknown ())
    | 'U' -> (
        match hex_value (start + 2) 8 with
        | Some value when is_scalar value -> foreign_escape (start + 10) value
        | _ -> unknown ())
    | 'a' -> foreign_escape (start + 2) 0x07
    | 'b' -> foreign_escape (start + 2) 0x08
    | 'f' -> foreign_escape (start + 2) 0x0C
    | 'v' -> foreign_escape (start + 2) 0x0B
    | 'e' -> foreign_escape (start + 2) 0x1B
    | '(' -> (
        (* Swift's interpolation, `\(name)`. *)
        let content = start + 2 in
        let rec close position =
          let current = byte cursor position in
          if current = Char.code ')' then Some position
          else if is_ascii_name_byte current || current = Char.code '.' then close (position + 1)
          else None
        in
        match close content with
        | Some stop when stop > content ->
            report cursor ~code:Invalid_escape
              ~fixes:
                [
                  Diagnostic.fix "Write `${...}`"
                    [
                      Diagnostic.replace (span start content) "${";
                      Diagnostic.replace (span stop (stop + 1)) "}";
                    ];
                ]
              (span start (stop + 1))
              "A string interpolates with `${...}`.";
            Buffer.add_substring buffer cursor.text start (stop + 1 - start);
            cursor.position <- stop + 1;
            `Continue
        | _ -> unknown ())
    | '\'' ->
        report cursor ~code:Invalid_escape
          ~fixes:[ Diagnostic.fix "Write `'`" [ Diagnostic.replace (span start (start + 2)) "'" ] ]
          (span start (start + 2))
          "`'` needs no escape in a string.";
        simple '\''
    | _ -> unknown ()

(* At the dollar signs or quotes that open a raw string. *)
and scan_raw cursor ~scan ~tag ~nesting ~dollars ~quotes =
  let delimiter_start = cursor.position in
  let literal_start =
    match tag with Some (_, (tag_span : span)) -> tag_span.start | None -> delimiter_start
  in
  let delimiter_stop = delimiter_start + dollars + quotes in
  let line_end = end_of_line cursor delimiter_stop in
  let multi_line = skip_spaces cursor delimiter_stop = line_end in
  let form = Raw { quotes; dollars; multi_line } in
  if not multi_line then begin
    cursor.position <- delimiter_stop;
    scan_one_line_raw cursor ~scan ~tag ~form ~nesting ~literal_start ~dollars ~quotes
  end
  else if nesting > 0 then begin
    report cursor ~code:Line_break_in_interpolation (span literal_start line_end)
      "An interpolation cannot contain a line break, so it cannot hold a multi-line string. Move \
       the expression into a `let` before the string.";
    cursor.position <- line_end;
    (literal ~tag ~form (builder delimiter_stop) delimiter_stop, Unterminated)
  end
  else
    ( scan_multi_line_raw cursor ~scan ~tag ~form ~literal_start ~dollars ~quotes ~delimiter_stop
        ~line_end,
      Closed )

(* A run of `$` in a raw string's body: text, or the start of an
   interpolation, which a run of at least max(n, 1) `$`s followed by `{`
   begins. The first `$`s of a longer run are text. *)
and raw_dollars cursor builder ~scan ~dollars ~nesting =
  let start = cursor.position in
  let run = run_length cursor start dollar in
  let needed = max dollars 1 in
  if run >= needed && byte cursor (start + run) = Char.code '{' then begin
    Buffer.add_string builder.buffer (String.make (run - needed) '$');
    cursor.position <- start + run - needed;
    let interpolation, ending =
      scan_interpolation cursor ~scan ~nesting ~delimiter_length:(needed + 1)
    in
    add_interpolation builder interpolation;
    ending
  end
  else begin
    Buffer.add_string builder.buffer (String.make run '$');
    cursor.position <- start + run;
    Closed
  end

and too_many_quotes cursor ~start ~run ~quotes ~multi_line =
  report cursor ~code:Raw_string_quotes
    (span start (start + run))
    (Printf.sprintf "A run of %d `\"`s is longer than this string's delimiter of %d.%s" run quotes
       (if multi_line then " Open the string with a longer delimiter."
        else
          " A one-line raw string cannot start or end with `\"`; use the multi-line form, or a \
           longer delimiter."))

and scan_one_line_raw cursor ~scan ~tag ~form ~nesting ~literal_start ~dollars ~quotes =
  let builder = builder cursor.position in
  let delimiter = String.make quotes '"' in
  let rec loop () =
    Source_text.copy_plain cursor builder.buffer ~special:raw_special;
    let position = cursor.position in
    let current = byte cursor position in
    if is_end_of_line current then begin
      let fixes =
        if nesting = 0 && byte cursor (position - 1) <> quote then
          [
            Diagnostic.fix
              ("Close the string with `" ^ delimiter ^ "`")
              [ Diagnostic.insert position delimiter ];
          ]
        else []
      in
      report cursor ~code:Unterminated_string ~fixes (span literal_start position)
        (Printf.sprintf
           "This raw string is not closed on its line. A raw string with text after its opening \
            `%s` is a one-line string. For several lines, start the text on the line after the \
            opening `%s`."
           delimiter delimiter);
      (Unterminated, position)
    end
    else if current = quote then begin
      let run = run_length cursor position quote in
      cursor.position <- position + run;
      if run >= quotes then begin
        if run > quotes then too_many_quotes cursor ~start:position ~run ~quotes ~multi_line:false;
        (Closed, position)
      end
      else begin
        Buffer.add_string builder.buffer (String.make run '"');
        loop ()
      end
    end
    else if current = dollar then
      match raw_dollars cursor builder ~scan ~dollars ~nesting with
      | Closed -> loop ()
      | Unterminated -> (Unterminated, cursor.position)
    else begin
      Source_text.read_character cursor builder.buffer ~context:Raw_string;
      loop ()
    end
  in
  let ending, stop = loop () in
  (literal ~tag ~form builder stop, ending)

(* A multi-line raw string's body is scanned line by line. Each line's
   texts and interpolations are stored separately, so that the indentation
   can be removed once the closing line is found. An unterminated one runs to the end of the file, as in Rust,
   Python, and Go, with a note at the line where it seems to end. *)
and scan_multi_line_raw cursor ~scan ~tag ~form ~literal_start ~dollars ~quotes ~delimiter_stop
    ~line_end =
  match read_raw_lines cursor ~scan ~dollars ~quotes ~line_end with
  | `Closed (lines, closing) ->
      build_multi_line cursor ~tag ~form ~quotes ~delimiter_stop lines closing
  | `Unterminated lines ->
      cursor.unterminated_at_end <- true;
      let delimiter = String.make quotes '"' in
      let notes =
        (match guess_raw_string_end cursor ~literal_start ~line_end with
          | Some line_start ->
              [
                ( Source.zero_width line_start,
                  Printf.sprintf "The string may have been meant to end with `%s` before this line."
                    delimiter );
              ]
          | None -> [])
        @
        (* Python's empty triple-quoted string opens a raw string here. *)
        if quotes = 6 && dollars = 0 then
          [ (span (delimiter_stop - quotes) delimiter_stop, "For an empty string, write `\"\"`.") ]
        else []
      in
      report cursor ~code:Unterminated_string ~notes
        (span literal_start delimiter_stop)
        (Printf.sprintf
           "This raw string is never closed, so it runs to the end of the file. Close it with `%s` \
            on a line of its own."
           delimiter);
      build_multi_line cursor ~tag ~form ~quotes ~delimiter_stop lines
        (`Unterminated cursor.position)

and read_raw_lines cursor ~scan ~dollars ~quotes ~line_end =
  cursor.position <- line_end;
  if cursor.position < cursor.length then ignore (Source_text.consume_line_break cursor);
  let lines = ref [] in
  let rec line () =
    let line_start = cursor.position in
    if line_start >= cursor.length then `Unterminated (List.rev !lines)
    else
      let first = skip_spaces cursor line_start in
      if byte cursor first = quote && run_length cursor first quote >= quotes then begin
        let run = run_length cursor first quote in
        if run > quotes then too_many_quotes cursor ~start:first ~run ~quotes ~multi_line:true;
        cursor.position <- first + run;
        `Closed
          ( List.rev !lines,
            `Own_line (String.sub cursor.text line_start (first - line_start), first) )
      end
      else
        let builder = builder line_start in
        let record stop = lines := finish builder stop :: !lines in
        let rec content () =
          Source_text.copy_plain cursor builder.buffer ~special:raw_special;
          let position = cursor.position in
          let current = byte cursor position in
          if is_end_of_line current then begin
            record position;
            if current < 0 then `Unterminated (List.rev !lines)
            else begin
              ignore (Source_text.consume_line_break cursor);
              line ()
            end
          end
          else if current = quote then begin
            let run = run_length cursor position quote in
            cursor.position <- position + run;
            if run = quotes then begin
              record position;
              `Closed (List.rev !lines, `After_text position)
            end
            else begin
              (* A longer run after text is an error, and is text. *)
              if run > quotes then
                too_many_quotes cursor ~start:position ~run ~quotes ~multi_line:true;
              Buffer.add_string builder.buffer (String.make run '"');
              content ()
            end
          end
          else if current = dollar then begin
            (* An unterminated interpolation stops at the end of the line,
               where a line break is legal in this string. *)
            ignore (raw_dollars cursor builder ~scan ~dollars ~nesting:0);
            content ()
          end
          else begin
            Source_text.read_character cursor builder.buffer ~context:Raw_string;
            content ()
          end
        in
        content ()
  in
  line ()

(* The whitespace that starts a line, or [None] for a line that holds only
   whitespace. *)
and leading_whitespace ((first : text), rest) =
  let value = first.value in
  let rec count index =
    if index < String.length value && (value.[index] = ' ' || value.[index] = '\t') then
      count (index + 1)
    else index
  in
  let length = count 0 in
  if length = String.length value && Array.length rest = 0 then None
  else Some (String.sub value 0 length)

(* The longest run of whitespace that starts every line holding more than
   whitespace. *)
and common_indentation lines =
  let common first second =
    let length = min (String.length first) (String.length second) in
    let rec loop index =
      if index < length && first.[index] = second.[index] then loop (index + 1) else index
    in
    String.sub first 0 (loop 0)
  in
  List.fold_left
    (fun so_far line ->
      match (leading_whitespace line, so_far) with
      | None, _ -> so_far
      | Some prefix, None -> Some prefix
      | Some prefix, Some so_far -> Some (common prefix so_far))
    None lines
  |> Option.value ~default:""

(* Where an unterminated multi-line raw string was probably meant to end,
   for a note: before the first non-blank line indented less than the line
   holding the opening delimiter, or before the first line where a
   definition starts. *)
and guess_raw_string_end cursor ~literal_start ~line_end =
  let opener_line = Source.line_start cursor.source literal_start in
  let opener_indentation = skip_spaces cursor opener_line - opener_line in
  let rec search position =
    if position >= cursor.length then None
    else
      let line_start = position + line_break_length cursor position in
      if line_start >= cursor.length then None
      else
        let first = skip_spaces cursor line_start in
        let blank = is_end_of_line (byte cursor first) in
        if
          ((not blank) && first - line_start < opener_indentation)
          || Layout.starts_definition cursor.source line_start
        then Some line_start
        else search (end_of_line cursor line_start)
  in
  search line_end

(* Removes the indentation and joins the lines. *)
and build_multi_line cursor ~tag ~form ~quotes ~delimiter_stop lines closing =
  let indentation, delimiter_start =
    match closing with
    | `Own_line (indentation, delimiter_start) -> (indentation, delimiter_start)
    | `After_text start ->
        let indentation = common_indentation lines in
        report cursor ~code:Raw_string_closing_not_alone
          ~fixes:
            [
              Diagnostic.fix "Move the closing delimiter to its own line"
                [ Diagnostic.insert start ("\n" ^ indentation) ];
            ]
          (span start (start + quotes))
          "The closing delimiter of a multi-line raw string goes on a line of its own.";
        (indentation, start)
    | `Unterminated position -> (common_indentation lines, position)
  in
  let describe_whitespace whitespace =
    if whitespace = "" then "no indentation"
    else
      let rec groups index =
        if index >= String.length whitespace then []
        else
          let character = whitespace.[index] in
          let rec stop position =
            if position < String.length whitespace && whitespace.[position] = character then
              stop (position + 1)
            else position
          in
          let next = stop index in
          let count = next - index in
          Printf.sprintf "%d %s%s" count
            (if character = '\t' then "tab" else "space")
            (if count = 1 then "" else "s")
          :: groups next
      in
      String.concat " then " (groups 0)
  in
  let joined = builder delimiter_stop in
  List.iteri
    (fun index (((first : text), rest) as line) ->
      if index > 0 then Buffer.add_char joined.buffer '\n';
      let value = first.value in
      let stripped =
        if String.starts_with ~prefix:indentation value then
          String.sub value (String.length indentation)
            (String.length value - String.length indentation)
        else if leading_whitespace line = None then ""
        else begin
          let length = min (String.length value) (String.length indentation) in
          let rec differs index =
            if index < length && value.[index] = indentation.[index] then differs (index + 1)
            else index
          in
          let at = differs 0 in
          let line_whitespace = Option.value (leading_whitespace line) ~default:"" in
          (* The line most likely belongs at the closing delimiter's
             indentation, as the lines around it are. *)
          report cursor ~code:Raw_string_indentation
            ~fixes:
              [
                Diagnostic.fix "Indent the line like the closing delimiter"
                  [
                    Diagnostic.replace
                      (span first.span.start (first.span.start + String.length line_whitespace))
                      indentation;
                  ];
              ]
            (span (first.span.start + at) (first.span.start + at + 1))
            (Printf.sprintf
               "Every line of a multi-line raw string starts with the indentation of its closing \
                delimiter, which is %s. This line starts with %s."
               (describe_whitespace indentation)
               (describe_whitespace line_whitespace));
          String.sub value at (String.length value - at)
        end
      in
      Buffer.add_string joined.buffer stripped;
      Array.iter
        (fun (interpolation, (text : text)) ->
          add_interpolation joined interpolation;
          Buffer.add_string joined.buffer text.value)
        rest)
    lines;
  literal ~tag ~form joined delimiter_start

(* A character literal from another language, `'a'` or `'\n'`, whose
   opening quote is at the cursor and which ends at [stop]: reported, with a
   fix to the tagged string `Character"a"`, which is the token it becomes.
   [literal_start] is where the literal starts, which is before the quote
   for a byte literal, `b'a'`, whose [tag] is `UInt8`. *)
let character_literal cursor ~tag ~literal_start ~stop =
  let start = cursor.position in
  let content = String.sub cursor.text (start + 1) (stop - start - 2) in
  let as_ordinary = match content with "\"" -> "\\\"" | "\\'" -> "'" | other -> other in
  let value =
    match content with
    | "\\n" -> "\n"
    | "\\t" -> "\t"
    | "\\r" -> "\r"
    | "\\0" -> "\000"
    | "\\\\" -> "\\"
    | "\\\"" -> "\""
    | "\\'" -> "'"
    | escape when String.starts_with ~prefix:"\\u{" escape -> (
        match int_of_string_opt ("0x" ^ String.sub escape 3 (String.length escape - 4)) with
        | Some value when value <= 0x10FFFF && (value < 0xD800 || value > 0xDFFF) ->
            Unicode.of_code_points [ value ]
        | _ -> "")
    | other -> other
  in
  let replacement = tag ^ "\"" ^ as_ordinary ^ "\"" in
  report cursor ~code:Character_literal
    ~fixes:
      [
        Diagnostic.fix
          ("Write `" ^ replacement ^ "`")
          [ Diagnostic.replace (span literal_start stop) replacement ];
      ]
    (span literal_start stop)
    (Printf.sprintf "Truss has no %s literals. A single %s is a tagged string: `%s`."
       (if tag = "UInt8" then "byte" else "character")
       (if tag = "UInt8" then "byte" else "character")
       replacement);
  cursor.position <- stop;
  String
    {
      tag = Some (tag, Source.zero_width literal_start);
      form = Ordinary;
      first = { value; span = span (start + 1) (stop - 1) };
      rest = [||];
    }

(* The edits that turn the text of a Python f-string, between [start] and
   [stop], into a Truss string's: `{name}` becomes `${name}`, and `{{` and
   `}}` become `{` and `}`. [None] when a replacement field is not an
   expression alone, as `{value:.2f}` and `{}` are not, since no exact fix
   exists then. *)
let format_field_edits cursor ~start ~stop =
  let plain current =
    is_ascii_name_byte current || is_space current
    || List.mem (Char.chr current) [ '.'; ','; '('; ')'; '['; ']'; '+'; '-'; '*'; '/' ]
  in
  let rec field_end position =
    if position >= stop then None
    else if byte cursor position = Char.code '}' then Some position
    else if plain (byte cursor position) then field_end (position + 1)
    else None
  in
  let rec edits position found =
    if position >= stop then Some (List.rev found)
    else
      let current = Char.chr (byte cursor position) and next = byte cursor (position + 1) in
      match current with
      | '\\' -> edits (position + 2) found
      | ('{' | '}') when next = Char.code current ->
          edits (position + 2)
            (Diagnostic.replace (span position (position + 2)) (String.make 1 current) :: found)
      | '{' -> (
          match field_end (position + 1) with
          | Some close when skip_spaces cursor (position + 1) < close ->
              edits (close + 1) (Diagnostic.insert position "$" :: found)
          | _ -> None)
      | _ -> edits (position + 1) found
  in
  edits start []

(* What a string prefix of another language means. *)
type prefix_kind = Format | Raw_text | Bytes

let prefix_kind = function "f" | "$" -> Format | "r" | "@" -> Raw_text | _ -> Bytes

(* A string with a prefix from another language: `f"..."`, `r"..."`, and
   `b"..."` of Python and Rust, `$"..."` and `@"..."` of C#, and Python's
   `f"""..."""` and `r"""..."""`. The cursor is at the first quote after the
   prefix, which starts at [start]. The prefix is reported, and the token is
   the string that the fix writes: an ordinary string for a format string
   and a byte string, and a raw string for raw text and for three quotes. *)
let prefixed_string cursor ~scan ~prefix ~start ~nesting =
  let quote_start = cursor.position in
  let quotes = run_length cursor quote_start quote in
  let empty = quotes = 2 in
  let kind_of_prefix = prefix_kind prefix in
  let remove_prefix = Diagnostic.delete (span start quote_start) in
  let kind, ending =
    if kind_of_prefix = Raw_text && quotes = 1 then begin
      cursor.position <- quote_start + 1;
      scan_one_line_raw cursor ~scan ~tag:None
        ~form:(Raw { quotes = 3; dollars = 0; multi_line = false })
        ~nesting ~literal_start:start ~dollars:0 ~quotes:1
    end
    else scan_string cursor ~scan ~tag:None ~nesting
  in
  let delimiter = if empty then 1 else quotes in
  let text_start = quote_start + delimiter and text_stop = cursor.position - delimiter in
  let closed =
    ending = Closed && text_stop >= text_start && run_length cursor text_stop quote >= delimiter
  in
  let has_interpolations =
    match kind with String { rest; _ } -> Array.length rest > 0 | _ -> false
  in
  let contains character =
    let rec search position =
      position < text_stop && (byte cursor position = Char.code character || search (position + 1))
    in
    search text_start
  in
  let message, fixes =
    match kind_of_prefix with
    | Format ->
        ( Printf.sprintf
            "Truss has no `%s` strings. Every string interpolates with `${...}`, as in `\"Hello \
             ${name}\"`."
            prefix,
          if (not closed) || has_interpolations then []
          else if empty then [ Diagnostic.fix "Remove the prefix" [ remove_prefix ] ]
          else if quotes >= 3 && contains '\\' then
            (* Python applies escapes in `f"""..."""`, and a raw string has none. *)
            []
          else
            match format_field_edits cursor ~start:text_start ~stop:text_stop with
            | Some edits ->
                [
                  Diagnostic.fix
                    (if quotes = 1 then "Write an ordinary string" else "Write a raw string")
                    (remove_prefix :: edits);
                ]
            | None -> [] )
    | Raw_text ->
        ( Printf.sprintf
            "Truss has no `%s` strings. A raw string, which has no escapes, is written between \
             `\"\"\"`s, as in `\"\"\"\\d+\"\"\"`."
            prefix,
          if (not closed) || has_interpolations then []
          else if empty || quotes >= 3 then [ Diagnostic.fix "Remove the prefix" [ remove_prefix ] ]
          else if
            byte cursor (text_stop - 1) = Char.code '\\'
            (* C# writes a quote in `@"..."` as `""`. *)
            || byte cursor (text_stop + 1) = quote
          then []
          else
            [
              Diagnostic.fix "Write a raw string"
                [
                  Diagnostic.replace (span start text_start) "\"\"\"";
                  Diagnostic.replace (span text_stop (text_stop + 1)) "\"\"\"";
                ];
            ] )
    | Bytes ->
        ( "Truss has no byte strings. A string is UTF-8 text, and `text.bytes()` gives its bytes.",
          [] )
  in
  report cursor ~code:String_prefix ~fixes (span start quote_start) message;
  (kind, ending)

(* Rust's raw string with hashes, `r#"..."#`, which starts at the `r` at
   [start]; the cursor is at its first `#`. [None] when it is not closed on
   its line. The token is the raw string that the fix writes, whose
   delimiter is longer than every run of quotes in the text. *)
let hash_raw_string cursor ~start =
  let hashes = run_length cursor cursor.position (Char.code '#') in
  let text_start = cursor.position + hashes + 1 in
  let line_end = end_of_line cursor text_start in
  let rec close position =
    if position >= line_end then None
    else if
      byte cursor position = quote && run_length cursor (position + 1) (Char.code '#') >= hashes
    then Some position
    else close (position + 1)
  in
  if byte cursor (text_start - 1) <> quote then None
  else
    match close text_start with
    | None -> None
    | Some text_stop ->
        let value = String.sub cursor.text text_start (text_stop - text_start) in
        let rec longest_run position longest =
          if position >= text_stop then longest
          else
            let run = run_length cursor position quote in
            longest_run (position + max run 1) (max longest run)
        in
        let quotes = max 3 (longest_run text_start 0 + 1) in
        let delimiter = String.make quotes '"' in
        (* A one-line raw string cannot start or end with a quote, a `${`
           in it would interpolate, and a character that needs checking
           would be reported only after the fix. *)
        let exact =
          value <> ""
          && value.[0] <> '"'
          && value.[String.length value - 1] <> '"'
          && String.for_all (fun c -> c >= ' ' && c < '\x7F') value
          &&
          let rec no_interpolation index =
            index + 1 >= String.length value
            || (not (value.[index] = '$' && value.[index + 1] = '{'))
               && no_interpolation (index + 1)
          in
          no_interpolation 0
        in
        let stop = text_stop + 1 + hashes in
        report cursor ~code:String_prefix
          ~fixes:
            (if exact then
               [
                 Diagnostic.fix "Write a raw string"
                   [
                     Diagnostic.replace (span start text_start) delimiter;
                     Diagnostic.replace (span text_stop stop) delimiter;
                   ];
               ]
             else [])
          (span start text_start)
          "Truss has no `r#` strings. A raw string is written between `\"\"\"`s, or between more \
           quotes when its text has `\"\"\"` in it.";
        cursor.position <- stop;
        Some
          (String
             {
               tag = None;
               form = Raw { quotes; dollars = 0; multi_line = false };
               first = { value; span = span text_start text_stop };
               rest = [||];
             })

(* Where the string that [delimiter] opens at [start] closes on its line:
   the offset of the next [delimiter] that no `\` escapes. *)
let closing_delimiter cursor ~start ~delimiter =
  let rec search position =
    let current = byte cursor position in
    if is_end_of_line current then None
    else if current = Char.code '\\' then search (position + 2)
    else if current = delimiter then Some position
    else search (position + 1)
  in
  search (start + 1)

(* A string of another language between single quotes or backticks, which
   closes on its line: scanned as an ordinary string, and reported with a
   fix that writes it between `"`s and escapes each `"` in its text. The
   cursor is at the opening delimiter. *)
let quoted_string cursor ~scan ~nesting ~delimiter =
  let start = cursor.position in
  let kind, ending = scan_ordinary cursor ~closing:delimiter ~scan ~tag:None ~nesting in
  let stop = cursor.position in
  let inside_interpolation position =
    match kind with
    | String { rest; _ } ->
        Array.exists
          (fun ((inner : interpolation), _) ->
            inner.span.start <= position && position < inner.span.stop)
          rest
    | _ -> false
  in
  let rec quote_edits position found =
    if position >= stop - 1 then List.rev found
    else if byte cursor position = Char.code '\\' then quote_edits (position + 2) found
    else if byte cursor position = quote && not (inside_interpolation position) then
      quote_edits (position + 1) (Diagnostic.insert position "\\" :: found)
    else quote_edits (position + 1) found
  in
  let template = delimiter = Char.code '`' in
  report cursor ~code:String_delimiter
    ~fixes:
      (if ending = Closed then
         [
           Diagnostic.fix "Write the string between `\"`s"
             ((Diagnostic.replace (span start (start + 1)) "\"" :: quote_edits (start + 1) [])
             @ [ Diagnostic.replace (span (stop - 1) stop) "\"" ]);
         ]
       else [])
    (span start (start + 1))
    (if template then
       "Truss has no template literals. Every string is written between `\"`s and interpolates \
        with `${...}`."
     else "A string is written between `\"`s.");
  (kind, ending)

(* Text between curly quotes, as a word processor writes a string: “text”
   or ‘text’. The cursor is at the opening quote, [opening_length] bytes
   long, and [closing] is the closing quote's encoding. [None] when it does
   not close on its line. *)
let curly_quoted_string cursor ~opening_length ~closing =
  let start = cursor.position in
  let text_start = start + opening_length in
  let line_end = end_of_line cursor text_start in
  let rec close position =
    if position + String.length closing > line_end then None
    else if String.sub cursor.text position (String.length closing) = closing then Some position
    else close (position + 1)
  in
  match close text_start with
  | None -> None
  | Some text_stop ->
      let value = String.sub cursor.text text_start (text_stop - text_start) in
      let stop = text_stop + String.length closing in
      (* Text that an ordinary string would read differently has no exact fix. *)
      let exact = String.for_all (fun c -> c >= ' ' && c <> '"' && c <> '\\' && c <> '$') value in
      report cursor ~code:Lookalike_character
        ~fixes:
          (if exact then
             [
               Diagnostic.fix "Write the string between `\"`s"
                 [
                   Diagnostic.replace (span start text_start) "\"";
                   Diagnostic.replace (span text_stop stop) "\"";
                 ];
             ]
           else [])
        (span start text_start)
        "A string is written between straight quotes, `\"`. This is a curly quote.";
      cursor.position <- stop;
      Some
        (String
           {
             tag = None;
             form = Ordinary;
             first = { value; span = span text_start text_stop };
             rest = [||];
           })

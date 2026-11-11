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

and scan_ordinary cursor ~scan ~tag ~nesting =
  let open_quote = cursor.position in
  let literal_start =
    match tag with Some (_, (tag_span : span)) -> tag_span.start | None -> open_quote
  in
  cursor.position <- open_quote + 1;
  let builder = builder cursor.position in
  (* Returns how the string ended and where its last text stops. *)
  let rec loop () =
    Source_text.copy_plain cursor builder.buffer ~special:ordinary_special;
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
    else if current = quote then begin
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
        if byte cursor (start + 2) <> Char.code '{' then problem (start + 2) form
        else
          let digits_start = start + 3 in
          let rec digits_end position =
            let current = byte cursor position in
            if
              is_digit current
              || (current >= 0x61 && current <= 0x66)
              || (current >= 0x41 && current <= 0x46)
            then digits_end (position + 1)
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
    | _ ->
        let packed = decode cursor (start + 1) in
        let length = if packed < 0 then 1 else Unicode.decoded_length packed in
        let written =
          if packed < 0 then
            Printf.sprintf "`\\` followed by %s" (show_character cursor (start + 1))
          else Printf.sprintf "`%s`" (String.sub cursor.text start (1 + length))
        in
        problem
          (start + 1 + length)
          (Printf.sprintf
             "%s is not an escape. The escapes are `\\n`, `\\t`, `\\r`, `\\0`, `\\\\`, `\\\"`, \
              `\\${`, and `\\u{...}`. For text with backslashes, such as a regular expression or a \
              Windows path, a raw string has no escapes: `\"\"\"\\d+\"\"\"`."
             written)

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

(* A character literal from another language, `'a'` or `'\n'`, ending at
   [stop]: reported, with a fix to the tagged string `Character"a"`, which
   is the token it becomes. *)
let character_literal cursor ~stop =
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
  let replacement = "Character\"" ^ as_ordinary ^ "\"" in
  report cursor ~code:Character_literal
    ~fixes:
      [
        Diagnostic.fix
          ("Write `" ^ replacement ^ "`")
          [ Diagnostic.replace (span start stop) replacement ];
      ]
    (span start stop)
    (Printf.sprintf "Truss has no character literals. A single character is a tagged string: `%s`."
       replacement);
  cursor.position <- stop;
  String
    {
      tag = Some ("Character", Source.zero_width start);
      form = Ordinary;
      first = { value; span = span (start + 1) (stop - 1) };
      rest = [||];
    }

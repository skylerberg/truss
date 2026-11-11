(* Inserts NEWLINE tokens and matches brackets, taking raw tokens from the
   scanner one at a time.

   The line-break rule is Scala's: outside ( and [, a line break becomes a
   NEWLINE when the token before it can end a statement and the token after
   it can begin one. *)

open Token

let can_end = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Close _ | Question) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable | Break | Continue | Return)
    ->
      true
  (* No grammar rule accepts the foreign tokens. Because `++` and `--` can
     both end and begin a statement, `i++` on a line of its own is a
     statement of its own, which the parser reports before it continues. *)
  | Foreign _ -> true
  | Keyword _ | Reserved _ | Punctuation _ | Newline | End_of_file -> false

let can_begin = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ | Foreign _ -> true
  | Punctuation (Open _ | Minus | Bang | Tilde) -> true
  | Keyword
      ( Any | Assert | Break | Capability | Concurrent | Continue | Echo | Exists | False | Fn | For
      | Forall | If | Impl | Internal | Law | Let | Match | Mut | Own | Parallel | Proof | Provide
      | Public | Return | Self_value | Self_type | Test | Theorem | Todo | Trait | True | Type
      | Unreachable | Use | Var | While | Yield ) ->
      true
  | Keyword
      ( Cost | Decreases | Derives | Else | Ensures | In | Indirect | Invariant | Is | Lends
      | Opaque | Requires | Transparent | Uses | With | Yields ) ->
      false
  | Punctuation _ | Newline | End_of_file -> false

(* Layout's input from the scanner: the next token with the line breaks
   before it, or the end of the input. On [Next], [unterminated] marks a
   string that ends at the end of its line with no closing quote. On [End],
   it says that the input ends inside an unterminated construct, an error
   the scanner already reported: an interpolation that a line break ended,
   or a file that ends inside a comment or a raw string. Brackets left open
   then are closed without another error. *)
type input =
  | Next of {
      kind : Token.kind;
      span : span;
      first_line_break : span option;
      blank_line : bool;
      unterminated : bool;
    }
  | End of {
      position : int;
      first_line_break : span option;
      blank_line : bool;
      unterminated : bool;
    }

type mode = File of { recovery : bool } | Interpolation

let token kind span = { kind; span; line_break_before = false; blank_line_before = false }
let spelling punctuation = punctuation_spelling punctuation
let opener_spelling bracket = spelling (Open bracket)
let closer_spelling bracket = spelling (Close bracket)

let is_name_byte c =
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') || c = '_'

let starts_definition source offset =
  Source.starts_line source offset
  &&
  let text = Source.text source in
  let rec word_end index =
    if index < String.length text && is_name_byte text.[index] then word_end (index + 1) else index
  in
  let stop = word_end offset in
  stop > offset
  &&
  match Token.word (String.sub text offset (stop - offset)) with
  | Some (Keyword keyword) -> List.mem keyword definition_keywords
  | _ -> false

(* The offset of the zero-width closers inserted before a token: the first
   line break before the token, so that the closers precede the NEWLINE
   that may follow them and the tokens stay ordered by offset. *)
let closer_position first_line_break position =
  match first_line_break with Some (line_break : span) -> line_break.start | None -> position

let indentation_of source offset =
  let text = Source.text source in
  let start = Source.line_start source offset in
  let rec stop index =
    if index < String.length text && (text.[index] = ' ' || text.[index] = '\t') then
      stop (index + 1)
    else index
  in
  String.sub text start (stop start - start)

(* An open bracket: its token's span, and its token's index in the output. *)
type opener = { bracket : bracket; span : span; index : int }

(* Where to insert the closer for the unclosed bracket [opener]: the offset,
   and whether it follows an indented line, or [None] if there is no good
   place. The indentation says where the bracket was meant to close: after
   the last line, among the elements directly inside it, indented more than
   the opener's line, or else on the opener's line. An element is a token or
   a whole nested group, so the closer is never put inside a nested group,
   or inside a comment that ends the line. An unterminated string probably
   contains the closer, and closing the string is the fix that matters, so
   then there is no good place.

   [tokens] is the output so far, and [closers] holds, for each opener in
   it that is closed, the index of its closer, so that a nested group is
   one step. The scan therefore visits only the bracket's own elements,
   which keeps closing every open bracket linear in the number of tokens. *)
let closing_position source tokens ~closers ~is_unterminated_string (opener : opener) =
  let opener_line = Source.line_start source opener.span.start in
  let indentation = String.length (indentation_of source opener.span.start) in
  let last_on_opener_line = ref (Some opener.span.stop) and last_indented = ref None in
  let element ~start ~stop ~contains_closer =
    let place = if contains_closer then None else Some stop in
    let line = Source.line_start source start in
    if line = opener_line then last_on_opener_line := place
    else if String.length (indentation_of source start) > indentation then
      last_indented := Some place
  in
  let rec scan index =
    if index < Dynarray.length tokens then
      let (token : Token.t) = Dynarray.get tokens index in
      match token.kind with
      | Newline -> scan (index + 1)
      | Punctuation (Open _) ->
          let closer = Dynarray.get closers index in
          (* A nested bracket that is still open holds every token after it. *)
          if closer >= 0 then begin
            element ~start:token.span.start ~stop:(Dynarray.get tokens closer).span.stop
              ~contains_closer:false;
            scan (closer + 1)
          end
      | _ ->
          element ~start:token.span.start ~stop:token.span.stop
            ~contains_closer:(is_unterminated_string token.span);
          scan (index + 1)
  in
  scan (opener.index + 1);
  match !last_indented with
  | Some place -> Option.map (fun stop -> (stop, true)) place
  | None -> Option.map (fun stop -> (stop, false)) !last_on_opener_line

(* The edits that close [openers], innermost first, or [None] if one has no
   good place. Each closer comes at or after the ones inside it. A `}`
   closing after an indented line goes on a line of its own, at the
   opener's indentation. *)
let closing_edits source tokens ~closers ~is_unterminated_string openers =
  let rec edits earliest reversed = function
    | [] -> Some (List.rev reversed)
    | (opener : opener) :: outer -> (
        match closing_position source tokens ~closers ~is_unterminated_string opener with
        | None -> None
        | Some (position, own_line) ->
            let position = max position earliest in
            let closer = closer_spelling opener.bracket in
            let replacement =
              if own_line && opener.bracket = Curly then
                "\n" ^ indentation_of source opener.span.start ^ closer
              else closer
            in
            edits position (Diagnostic.insert position replacement :: reversed) outer)
  in
  edits 0 [] openers

let bracket_index = function Paren -> 0 | Square -> 1 | Curly -> 2

let run ~source ~diagnostics ~mode next_input =
  let output = Dynarray.create () in
  (* For each opener in [output] that is closed, the index of its closer;
     for every other token, -1. *)
  let closers = Dynarray.create () in
  (* Open brackets, innermost first, and how many of each bracket are open,
     so that a closer that matches nothing is found without a search. *)
  let stack : opener list ref = ref [] in
  let open_count = Array.make 3 0 in
  let previous = ref None in
  let open_at_end = ref false in
  (* The start offset of each unterminated string. *)
  let unterminated_strings = Hashtbl.create 4 in
  let is_unterminated_string (span : span) = Hashtbl.mem unterminated_strings span.start in
  let emit token =
    Dynarray.add_last output token;
    Dynarray.add_last closers (-1);
    previous := Some token.kind
  in
  let report diagnostic = Diagnostic.Collector.add diagnostics diagnostic in
  let push bracket span =
    stack := { bracket; span; index = Dynarray.length output } :: !stack;
    open_count.(bracket_index bracket) <- open_count.(bracket_index bracket) + 1
  in
  (* Emits [closer] for the innermost open bracket. *)
  let pop closer =
    match !stack with
    | opener :: rest ->
        stack := rest;
        open_count.(bracket_index opener.bracket) <- open_count.(bracket_index opener.bracket) - 1;
        Dynarray.set closers opener.index (Dynarray.length output);
        emit closer
    | [] -> ()
  in
  let insert_closer position =
    match !stack with
    | opener :: _ -> pop (token (Punctuation (Close opener.bracket)) (Source.zero_width position))
    | [] -> ()
  in
  let close_silently position =
    while !stack <> [] do
      insert_closer position
    done
  in
  let closing_fix openers ~title =
    match closing_edits source output ~closers ~is_unterminated_string openers with
    | Some edits -> [ Diagnostic.fix title edits ]
    | None -> []
  in
  (* Closes every open bracket with zero-width closers at [position]. The
     innermost is reported, with one fix that closes them all where the
     indentation says each was meant to close. *)
  let close_all ~position ~reason =
    match !stack with
    | [] -> ()
    | innermost :: outer ->
        let closers =
          String.concat "" (List.map (fun opener -> closer_spelling opener.bracket) !stack)
        in
        let notes =
          List.map
            (fun opener ->
              ( opener.span,
                Printf.sprintf "This `%s` is not closed either." (opener_spelling opener.bracket) ))
            outer
        in
        report
          (Diagnostic.make ~code:(Lexer Unclosed_bracket) ~notes
             ~fixes:(closing_fix !stack ~title:(Printf.sprintf "Insert `%s`" closers))
             innermost.span
             (Printf.sprintf "This `%s` is never closed%s."
                (opener_spelling innermost.bracket)
                reason));
        close_silently position
  in
  let close_bracket (current : Token.t) bracket =
    let span = current.span in
    if open_count.(bracket_index bracket) = 0 then
      report
        (Diagnostic.make ~code:(Lexer Unmatched_closing_bracket) span
           (Printf.sprintf "This `%s` has no `%s` to close." (closer_spelling bracket)
              (opener_spelling bracket)))
    else begin
      (* Openers above the match were never closed. *)
      let rec close_unclosed () =
        match !stack with
        | opener :: _ when opener.bracket <> bracket ->
            report
              (Diagnostic.make ~code:(Lexer Unclosed_bracket)
                 ~notes:
                   [
                     ( span,
                       Printf.sprintf "This `%s` closes an earlier `%s` first."
                         (closer_spelling bracket) (opener_spelling bracket) );
                   ]
                 ~fixes:
                   (closing_fix [ opener ]
                      ~title:(Printf.sprintf "Insert `%s`" (closer_spelling opener.bracket)))
                 opener.span
                 (Printf.sprintf "This `%s` is never closed." (opener_spelling opener.bracket)));
            insert_closer span.start;
            close_unclosed ()
        | _ -> ()
      in
      close_unclosed ();
      pop current
    end
  in
  let finish ~position ~first_line_break ~blank_line ~unterminated =
    if !stack <> [] then open_at_end := true;
    (match mode with
    | File _ when unterminated -> close_silently (closer_position first_line_break position)
    | Interpolation when unterminated -> close_silently position
    | File _ ->
        close_all
          ~position:(closer_position first_line_break position)
          ~reason:" before the end of the file"
    | Interpolation -> close_all ~position ~reason:" before the end of the interpolation");
    (match (mode, !previous) with
    | File _, Some previous_kind when can_end previous_kind ->
        emit
          (token Newline
             (match first_line_break with Some span -> span | None -> Source.zero_width position))
    | _ -> ());
    emit
      {
        kind = End_of_file;
        span = Source.zero_width position;
        line_break_before = first_line_break <> None;
        blank_line_before = blank_line;
      };
    Dynarray.to_array output
  in
  let rec loop () =
    match next_input () with
    | End { position; first_line_break; blank_line; unterminated } ->
        finish ~position ~first_line_break ~blank_line ~unterminated
    | Next { kind; span; first_line_break; blank_line; unterminated } ->
        (match mode with
        | File { recovery = true } when !stack <> [] && starts_definition source span.start ->
            close_all
              ~position:(closer_position first_line_break span.start)
              ~reason:" before the next definition"
        | _ -> ());
        let ignores_line_breaks =
          match !stack with { bracket = Paren | Square; _ } :: _ -> true | _ -> false
        in
        (match (first_line_break, !previous) with
        | Some line_break, Some previous_kind
          when (not ignores_line_breaks) && can_end previous_kind && can_begin kind ->
            emit (token Newline line_break)
        | _ -> ());
        if unterminated then Hashtbl.replace unterminated_strings span.start ();
        let current =
          {
            kind;
            span;
            line_break_before = first_line_break <> None;
            blank_line_before = blank_line;
          }
        in
        (match kind with
        | Punctuation (Open bracket) ->
            push bracket span;
            emit current
        | Punctuation (Close bracket) -> close_bracket current bracket
        | _ -> emit current);
        loop ()
  in
  let tokens = loop () in
  (tokens, !open_at_end)

let file ~source ~diagnostics ~recovery next_input =
  run ~source ~diagnostics ~mode:(File { recovery }) next_input

let interpolation ~source ~diagnostics next_input =
  fst (run ~source ~diagnostics ~mode:Interpolation next_input)

type input =
  | Next of {
      kind : Token.kind;
      span : Source.span;
      first_line_break : Source.span option;
      blank_line : bool;
      unterminated_string : bool;
    }
  | End of {
      position : int;
      first_line_break : Source.span option;
      blank_line : bool;
      ends_unterminated : bool;
    }

type mode = File of { recovery : bool } | Interpolation

let token kind span =
  {
    Token.kind;
    span;
    line_break_before = false;
    blank_line_before = false;
    is_inserted_closer = false;
  }

let spelling punctuation = Token.punctuation_spelling punctuation
let opener_spelling bracket = spelling (Open bracket)
let closer_spelling bracket = spelling (Close bracket)

let is_name_byte character =
  (character >= 'a' && character <= 'z')
  || (character >= 'A' && character <= 'Z')
  || (character >= '0' && character <= '9')
  || character = '_'

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
  | Some (Keyword keyword) -> List.mem keyword Token.definition_keywords
  | _ -> false

let indentation_of source offset =
  let text = Source.text source in
  let start = Source.line_start source offset in
  let rec stop index =
    if index < String.length text && (text.[index] = ' ' || text.[index] = '\t') then
      stop (index + 1)
    else index
  in
  String.sub text start (stop start - start)

let token_starts_definition source ~first_line_break (kind : Token.kind) offset =
  first_line_break <> None
  && indentation_of source offset = ""
  && match kind with Keyword keyword -> List.mem keyword Token.definition_keywords | _ -> false

let closer_position first_line_break position =
  match first_line_break with
  | Some (line_break : Source.span) -> line_break.start
  | None -> position

type opener = { bracket : Token.bracket; span : Source.span; index : int }

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
            edits position
              (Diagnostic.insert (Source.zero_width position) replacement :: reversed)
              outer)
  in
  edits 0 [] openers

let bracket_index = function Token.Paren -> 0 | Square -> 1 | Curly -> 2

let run ~source ~diagnostics ~mode next_input =
  let output = Dynarray.create () in
  let closers = Dynarray.create () in
  let stack : opener list ref = ref [] in
  let open_count = Array.make 3 0 in
  let previous = ref None in
  let open_at_end = ref false in
  let unterminated_strings = Hashtbl.create 4 in
  let is_unterminated_string (span : Source.span) = Hashtbl.mem unterminated_strings span.start in
  let emit (token : Token.t) =
    Dynarray.add_last output token;
    Dynarray.add_last closers (-1);
    previous := Some token.kind
  in
  let report diagnostic = Diagnostic.Collector.add diagnostics diagnostic in
  let push bracket span =
    stack := { bracket; span; index = Dynarray.length output } :: !stack;
    open_count.(bracket_index bracket) <- open_count.(bracket_index bracket) + 1
  in
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
  let finish ~position ~first_line_break ~blank_line ~ends_unterminated =
    if !stack <> [] then open_at_end := true;
    (match mode with
    | File _ when ends_unterminated -> close_silently (closer_position first_line_break position)
    | Interpolation when ends_unterminated -> close_silently position
    | File _ ->
        close_all
          ~position:(closer_position first_line_break position)
          ~reason:" before the end of the file"
    | Interpolation -> close_all ~position ~reason:" before the end of the interpolation");
    (match (mode, !previous) with
    | File _, Some previous_kind when Token.can_end previous_kind ->
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
        is_inserted_closer = false;
      };
    Dynarray.to_array output
  in
  let rec loop () =
    match next_input () with
    | End { position; first_line_break; blank_line; ends_unterminated } ->
        finish ~position ~first_line_break ~blank_line ~ends_unterminated
    | Next { kind; span; first_line_break; blank_line; unterminated_string } ->
        (match mode with
        | File { recovery = true }
          when !stack <> [] && token_starts_definition source ~first_line_break kind span.start ->
            close_all
              ~position:(closer_position first_line_break span.start)
              ~reason:" before the next definition"
        | _ -> ());
        let ignores_line_breaks =
          match !stack with { bracket = Paren | Square; _ } :: _ -> true | _ -> false
        in
        (match (first_line_break, !previous) with
        | Some line_break, Some previous_kind
          when (not ignores_line_breaks) && Token.can_end previous_kind && Token.can_begin kind ->
            emit (token Newline line_break)
        | _ -> ());
        if unterminated_string then Hashtbl.replace unterminated_strings span.start ();
        let current =
          {
            Token.kind;
            span;
            line_break_before = first_line_break <> None;
            blank_line_before = blank_line;
            is_inserted_closer = false;
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

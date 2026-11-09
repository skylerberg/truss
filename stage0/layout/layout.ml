(* Inserts NEWLINE tokens and matches brackets, pulling raw tokens one at a
   time. See LEXER.md, "Layout".

   The line-break rule is GRAMMAR.md's, which is Scala's: outside ( and [, a
   line break becomes a NEWLINE when the token before it can end a statement
   and the token after it can begin one. *)

open Token

let can_end = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Close _ | Question) -> true
  | Keyword (True | False | Self_value | Self_type | Todo | Unreachable | Break | Continue | Return)
    ->
      true
  (* GRAMMAR.md leaves out the foreign tokens, which no rule accepts. Treating
     `++` and `--` as both ending and beginning a statement keeps `i++` on a
     line of its own apart from its neighbors, so the parser can report it
     and go on. *)
  | Foreign _ -> true
  | Keyword _ | Reserved _ | Punctuation _ | Newline | End_of_file -> false

let can_begin = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ | Foreign _ -> true
  | Punctuation (Open _ | Minus | Bang | Tilde) -> true
  | Keyword
      ( Any | Assert | Break | Capability | Continue | Echo | Exists | False | Fn | For | Forall
      | If | Impl | Internal | Law | Let | Match | Mut | Own | Parallel | Proof | Provide | Public
      | Return | Self_value | Self_type | Test | Theorem | Todo | Trait | True | Type | Unreachable
      | Use | Var | While | Yield ) ->
      true
  | Keyword
      ( Cost | Decreases | Derives | Else | Ensures | In | Indirect | Invariant | Is | Lends
      | Opaque | Requires | Uses | With | Yields ) ->
      false
  | Punctuation _ | Newline | End_of_file -> false

(* What the scanner gives layout: the next token with the line breaks
   before it, or the end of the input. On [End], [cut_off] says whether the
   input ended at an error already reported: an interpolation cut off by a
   line break, or a file that ends inside an unterminated comment or string.
   Brackets left open then are closed without another error. On [Next], it
   says the token is a string cut off at the end of its line. *)
type input =
  | Next of {
      kind : Token.kind;
      span : span;
      first_line_break : span option;
      blank_line : bool;
      cut_off : bool;
    }
  | End of { position : int; first_line_break : span option; blank_line : bool; cut_off : bool }

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

(* Where zero-width closers go when brackets are closed before a token: at
   the first line break before it, so that they come before the NEWLINE that
   may follow them and the tokens stay in order of position. *)
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

(* Where to insert the closer for a bracket, opened at [opener], when it is
   found unclosed at [limit]: the offset, and whether it follows an indented
   line, or [None] if there is no good place. The indentation says where it
   was meant to close: after the last line, among the elements directly
   inside it, indented more than the opener's line, or else on the opener's
   line. An element is a token or a whole nested group, so the closer is
   never put inside a group nested in it, or inside a comment that ends the
   line. A string cut off at the end of its line probably swallowed the
   closer, and fixing the string is what matters, so then there is no good
   place. [tokens] are the tokens so far, which hold the opener; [cut_off]
   says which of them are strings cut off at the end of their line. *)
let closing_position source tokens ~cut_off (opener : span) ~limit =
  let opener_line = Source.line_start source opener.start in
  let indentation = String.length (indentation_of source opener.start) in
  let rec find index =
    if index < 0 then 0
    else if (Dynarray.get tokens index : Token.t).span.start = opener.start then index
    else find (index - 1)
  in
  let last_on_opener_line = ref (Some opener.stop) and last_indented = ref None in
  let element ~start ~stop ~swallows =
    let place = if swallows then None else Some stop in
    let line = Source.line_start source start in
    if line = opener_line then last_on_opener_line := place
    else if String.length (indentation_of source start) > indentation then
      last_indented := Some place
  in
  let depth = ref 1 and group_start = ref 0 in
  for index = find (Dynarray.length tokens - 1) + 1 to Dynarray.length tokens - 1 do
    let (token : Token.t) = Dynarray.get tokens index in
    if token.span.start < limit && token.kind <> Newline then
      match token.kind with
      | Punctuation (Open _) ->
          if !depth = 1 then group_start := token.span.start;
          incr depth
      | Punctuation (Close _) ->
          decr depth;
          if !depth = 1 then element ~start:!group_start ~stop:token.span.stop ~swallows:false
      | _ ->
          if !depth = 1 then
            element ~start:token.span.start ~stop:token.span.stop ~swallows:(cut_off token.span)
  done;
  match !last_indented with
  | Some place -> Option.map (fun stop -> (stop, true)) place
  | None -> Option.map (fun stop -> (stop, false)) !last_on_opener_line

(* The edits that close [openers], innermost first, or [None] if one has no
   good place. Each closer comes at or after the ones inside it. A `}`
   closing after an indented line goes on a line of its own, at the
   opener's indentation. *)
let closing_edits source tokens ~cut_off openers ~limit =
  let rec edits earliest = function
    | [] -> Some []
    | (bracket, (opener : span)) :: outer -> (
        match closing_position source tokens ~cut_off opener ~limit with
        | None -> None
        | Some (position, own_line) ->
            let position = max position earliest in
            let closer = closer_spelling bracket in
            let replacement =
              if own_line && bracket = Curly then "\n" ^ indentation_of source opener.start ^ closer
              else closer
            in
            Option.map
              (fun rest -> Diagnostic.insert position replacement :: rest)
              (edits position outer))
  in
  edits 0 openers

let run ~source ~diagnostics ~mode pull =
  let output = Dynarray.create () in
  (* Open brackets, innermost first. *)
  let stack : (bracket * span) list ref = ref [] in
  let previous = ref None in
  let open_at_end = ref false in
  (* The strings cut off at the end of their line, by where they start. *)
  let cut_off_strings = Hashtbl.create 4 in
  let cut_off (span : span) = Hashtbl.mem cut_off_strings span.start in
  let emit token =
    Dynarray.add_last output token;
    previous := Some token.kind
  in
  let report diagnostic = Diagnostic.Collector.add diagnostics diagnostic in
  let close position =
    match !stack with
    | (bracket, _) :: rest ->
        stack := rest;
        emit (token (Punctuation (Close bracket)) (Source.zero_width position))
    | [] -> ()
  in
  let close_silently position =
    while !stack <> [] do
      close position
    done
  in
  (* Closes every open bracket, found unclosed at [limit], with zero-width
     closers at [position]. The innermost is reported, with one fix that
     closes them all where the indentation says each was meant to close. *)
  let close_all ~position ~limit ~reason =
    match !stack with
    | [] -> ()
    | (innermost, innermost_span) :: outer ->
        let closers =
          String.concat "" (List.map (fun (bracket, _) -> closer_spelling bracket) !stack)
        in
        let notes =
          List.map
            (fun (bracket, span) ->
              (span, Printf.sprintf "This `%s` is not closed either." (opener_spelling bracket)))
            outer
        in
        report
          (Diagnostic.make ~code:(Lexer Unclosed_bracket) ~notes
             ~fixes:
               (match closing_edits source output ~cut_off !stack ~limit with
               | Some edits -> [ Diagnostic.fix (Printf.sprintf "Insert `%s`" closers) edits ]
               | None -> [])
             innermost_span
             (Printf.sprintf "This `%s` is never closed%s." (opener_spelling innermost) reason));
        close_silently position
  in
  let close_bracket (current : Token.t) bracket =
    let span = current.span in
    if not (List.exists (fun (candidate, _) -> candidate = bracket) !stack) then
      report
        (Diagnostic.make ~code:(Lexer Unmatched_closing_bracket) span
           (Printf.sprintf "This `%s` has no `%s` to close." (closer_spelling bracket)
              (opener_spelling bracket)))
    else begin
      (* Openers above the match were never closed. *)
      let rec close_unclosed () =
        match !stack with
        | (top, _) :: _ when top = bracket -> ()
        | ((unclosed, unclosed_span) as opener) :: _ ->
            report
              (Diagnostic.make ~code:(Lexer Unclosed_bracket)
                 ~notes:
                   [
                     ( span,
                       Printf.sprintf "This `%s` closes an earlier `%s` first."
                         (closer_spelling bracket) (opener_spelling bracket) );
                   ]
                 ~fixes:
                   (match closing_edits source output ~cut_off [ opener ] ~limit:span.start with
                   | Some edits ->
                       [
                         Diagnostic.fix
                           (Printf.sprintf "Insert `%s`" (closer_spelling unclosed))
                           edits;
                       ]
                   | None -> [])
                 unclosed_span
                 (Printf.sprintf "This `%s` is never closed." (opener_spelling unclosed)));
            close span.start;
            close_unclosed ()
        | [] -> ()
      in
      close_unclosed ();
      stack := List.tl !stack;
      emit current
    end
  in
  let finish ~position ~first_line_break ~blank_line ~cut_off =
    if !stack <> [] then open_at_end := true;
    (match (mode, !stack) with
    | _, [] -> ()
    | File _, _ :: _ when cut_off -> close_silently (closer_position first_line_break position)
    | Interpolation, _ :: _ when cut_off -> close_silently position
    | File _, _ :: _ ->
        close_all
          ~position:(closer_position first_line_break position)
          ~limit:position ~reason:" before the end of the file"
    | Interpolation, _ :: _ ->
        close_all ~position ~limit:position ~reason:" before the end of the interpolation");
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
    match pull () with
    | End { position; first_line_break; blank_line; cut_off } ->
        finish ~position ~first_line_break ~blank_line ~cut_off
    | Next { kind; span; first_line_break; blank_line; cut_off } ->
        (match mode with
        | File { recovery = true } when !stack <> [] && starts_definition source span.start ->
            close_all
              ~position:(closer_position first_line_break span.start)
              ~limit:span.start ~reason:" before the next definition"
        | _ -> ());
        let inside_parentheses =
          match !stack with ((Paren | Square), _) :: _ -> true | _ -> false
        in
        (match (first_line_break, !previous) with
        | Some line_break, Some previous_kind
          when (not inside_parentheses) && can_end previous_kind && can_begin kind ->
            emit (token Newline line_break)
        | _ -> ());
        if cut_off then Hashtbl.replace cut_off_strings span.start ();
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
            stack := (bracket, span) :: !stack;
            emit current
        | Punctuation (Close bracket) -> close_bracket current bracket
        | _ -> emit current);
        loop ()
  in
  let tokens = loop () in
  (tokens, !open_at_end)

let file ~source ~diagnostics ~recovery pull =
  run ~source ~diagnostics ~mode:(File { recovery }) pull

let interpolation ~source ~diagnostics pull =
  fst (run ~source ~diagnostics ~mode:Interpolation pull)

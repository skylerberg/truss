(* Inserts NEWLINE tokens and matches brackets, pulling raw tokens one at a
   time. See LEXER.md, "Layout".

   The line-break rule is GRAMMAR.md's, which is Scala's: outside ( and [, a
   line break becomes a NEWLINE when the token before it can end a statement
   and the token after it can begin one. *)

open Token

let can_end = function
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ -> true
  | Punctuation (Right_paren | Right_bracket | Right_brace | Question) -> true
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
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ | Foreign _ ->
      true
  | Punctuation (Left_paren | Left_bracket | Left_brace | Minus | Bang | Tilde) -> true
  | Keyword
      ( Any | Assert | Break | Capability | Continue | Echo | Exists | False | Fn | For | Forall
      | If | Impl | Internal | Law | Let | Match | Mut | Own | Parallel | Proof | Provide | Public
      | Return | Self_value | Self_type | Test | Theorem | Todo | Trait | True | Type
      | Unreachable | Use | Var | While | Yield ) ->
      true
  | Keyword
      ( Cost | Decreases | Derives | Else | Ensures | In | Invariant | Is | Opaque | Requires
      | Uses | With | Yields ) ->
      false
  | Punctuation _ | Newline | End_of_file -> false

type mode =
  | File of { recovery : bool }
      (** With [recovery], a definition keyword in column 0 closes every open
          bracket. Without it, brackets still open at the end of the file
          make {!run} return [None], so that the lexer can run again with
          recovery turned on. *)
  | Interpolation of { cut_off : unit -> bool }
      (** An interpolation's tokens: brackets still open at its end are
          closed there, and no NEWLINE comes at the end. [cut_off] says, at
          the end, whether the interpolation ended at an error the scanner
          has already reported rather than at its closing brace. Brackets
          left open by such an interpolation are closed without another
          error. *)

let zero_width position = { start = position; stop = position }
let token kind span = { kind; span; line_break_before = false; blank_line_before = false }
let spelling punctuation = punctuation_spelling punctuation

let closer_spelling opener =
  match closer_of opener with Some closer -> spelling closer | None -> assert false

(* Where zero-width closers go when brackets are closed before a token: at
   the first line break before it, so that they come before the NEWLINE that
   may follow them and the tokens stay in order of position. *)
let closer_position first_line_break position =
  match first_line_break with Some line_break -> line_break.start | None -> position

let is_whitespace text start stop =
  let rec loop index =
    index >= stop || (match text.[index] with ' ' | '\t' | '\n' | '\r' -> loop (index + 1) | _ -> false)
  in
  loop start

(* Whether [token] is a multi-line raw string that ends at [position]
   without its closing delimiter: one the scanner found unterminated and
   ended at the end of the file or before a line where it seems to end.
   Text inserted at [position] would become part of it. *)
let ends_inside_raw_string text (token : Token.t) position =
  match token.kind with
  | String { tag; form = Raw { multi_line = true; quotes; dollars }; _ } ->
      let opening_end =
        (match tag with Some (_, tag_span) -> tag_span.stop | None -> token.span.start) + dollars + quotes
      in
      (* A closed one ends with its delimiter, on a later line than the
         opening one. *)
      let closed =
        token.span.stop - quotes > opening_end
        && String.sub text (token.span.stop - quotes) quotes = String.make quotes '"'
      in
      token.span.stop = position && not closed
  | _ -> false

let is_definition_keyword = function
  | Keyword keyword -> List.mem keyword definition_keywords
  | _ -> false

let run ~source ~diagnostics ~mode pull =
  let output = Dynarray.create () in
  (* Open brackets, innermost first. *)
  let stack : (punctuation * span) list ref = ref [] in
  let previous = ref None in
  (* The last token from the scanner, as opposed to an inserted one. *)
  let last_token = ref None in
  let emit token =
    Dynarray.add_last output token;
    previous := Some token.kind
  in
  let report diagnostic = Diagnostic.Collector.add diagnostics diagnostic in
  let close position =
    let opener, _ = List.hd !stack in
    stack := List.tl !stack;
    match closer_of opener with
    | Some closer -> emit (token (Punctuation closer) (zero_width position))
    | None -> assert false
  in
  (* Closes every open bracket at [position], reporting the innermost one with
     a fix that inserts [before ^ closers ^ after] at the offset [fix] gives,
     if it gives one. *)
  let close_all ~position ~fix ~reason =
    match !stack with
    | [] -> ()
    | (innermost, innermost_span) :: outer ->
        let closers = String.concat "" (List.map (fun (opener, _) -> closer_spelling opener) !stack) in
        let notes =
          List.map
            (fun (opener, span) ->
              (span, Printf.sprintf "This `%s` is not closed either." (spelling opener)))
            outer
        in
        report
          (Diagnostic.make ~code:"lexer.unclosed_bracket" ~notes
             ~fixes:
               (match fix with
               | Some (fix_position, before, after) ->
                   [
                     Diagnostic.fix
                       (Printf.sprintf "Insert `%s`" closers)
                       [ Diagnostic.insert fix_position (before ^ closers ^ after) ];
                   ]
               | None -> [])
             innermost_span
             (Printf.sprintf "This `%s` is never closed%s." (spelling innermost) reason));
        while !stack <> [] do
          close position
        done
  in
  let rec loop () =
    let { token = current; first_line_break } = pull () in
    match current.kind with
    | End_of_file -> finish current first_line_break
    | kind ->
        (match mode with
        | File { recovery = true }
          when !stack <> []
               && is_definition_keyword kind
               && Source.starts_line source current.span.start ->
            close_all ~position:(closer_position first_line_break current.span.start)
              ~fix:
                (match !last_token with
                | Some last when ends_inside_raw_string (Source.text source) last current.span.start ->
                    None
                | _ -> Some (current.span.start, "", "\n")) ~reason:" before the next definition"
        | _ -> ());
        let inside_parentheses =
          match !stack with ((Left_paren | Left_bracket), _) :: _ -> true | _ -> false
        in
        (match (first_line_break, !previous) with
        | Some line_break, Some previous_kind
          when (not inside_parentheses) && can_end previous_kind && can_begin kind ->
            emit (token Newline line_break)
        | _ -> ());
        (match kind with
        | Punctuation ((Left_paren | Left_bracket | Left_brace) as opener) ->
            stack := (opener, current.span) :: !stack;
            emit current
        | Punctuation ((Right_paren | Right_bracket | Right_brace) as closer) ->
            close_bracket current closer
        | _ -> emit current);
        last_token := Some current;
        loop ()
  and close_bracket current closer =
    let opener = Option.get (opener_of closer) in
    if not (List.exists (fun (candidate, _) -> candidate = opener) !stack) then
      report
        (Diagnostic.make ~code:"lexer.unmatched_closing_bracket" current.span
           (Printf.sprintf "This `%s` has no `%s` to close." (spelling closer) (spelling opener)))
    else begin
      (* Openers above the match were never closed. *)
      while fst (List.hd !stack) <> opener do
        let unclosed, span = List.hd !stack in
        let missing = closer_spelling unclosed in
        report
          (Diagnostic.make ~code:"lexer.unclosed_bracket"
             ~notes:
               [
                 ( current.span,
                   Printf.sprintf "This `%s` closes an earlier `%s` first." (spelling closer)
                     (spelling opener) );
               ]
             ~fixes:
               [
                 Diagnostic.fix
                   (Printf.sprintf "Insert `%s`" missing)
                   [ Diagnostic.insert current.span.start missing ];
               ]
             span
             (Printf.sprintf "This `%s` is never closed." (spelling unclosed)));
        close current.span.start
      done;
      stack := List.tl !stack;
      emit current
    end
  and finish end_of_file first_line_break =
    let position = end_of_file.span.start in
    let complete () =
      (match (mode, !previous) with
      | File _, Some previous_kind when can_end previous_kind ->
          emit
            (token Newline
               (match first_line_break with Some span -> span | None -> zero_width position))
      | _ -> ());
      emit end_of_file;
      Some (Dynarray.to_array output)
    in
    match (mode, !stack) with
    | _, [] -> complete ()
    | File { recovery = false }, _ :: _ -> None
    | File { recovery = true }, _ :: _ ->
        let text = Source.text source in
        let fix =
          match !last_token with
          | Some last when ends_inside_raw_string text last position ->
              (* Anything inserted at the end would be inside the string. *)
              None
          | Some last when not (is_whitespace text last.span.stop position) ->
              (* An unterminated comment runs to the end of the file, so the
                 closers go right after the last token. *)
              Some (last.span.stop, "\n", "")
          | _ ->
              let ends_with_line_break =
                position > 0 && (text.[position - 1] = '\n' || text.[position - 1] = '\r')
              in
              Some
                ( position,
                  (if ends_with_line_break || position = 0 then "" else "\n"),
                  if ends_with_line_break then "\n" else "" )
        in
        close_all ~position:(closer_position first_line_break position) ~fix
          ~reason:" before the end of the file";
        complete ()
    | Interpolation { cut_off }, _ :: _ ->
        if cut_off () then
          while !stack <> [] do
            close position
          done
        else
          close_all ~position ~fix:(Some (position, "", "")) ~reason:" before the end of the interpolation";
        complete ()
  in
  loop ()

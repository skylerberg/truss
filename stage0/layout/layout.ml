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
  | Upper _ | Lower _ | Underscore | Integer _ | Float _ | String _ | Reserved _ | Foreign _ ->
      true
  | Punctuation (Open _ | Minus | Bang | Tilde) -> true
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

(* [cut_off] says, at the end, whether the input ended at an error already
   reported: an interpolation cut off by a line break, or a file that ends
   inside an unterminated comment or string. Brackets left open then are
   closed without another error. *)
type mode = File of { recovery : bool; cut_off : unit -> bool } | Interpolation of { cut_off : unit -> bool }

let token kind span = { kind; span; line_break_before = false; blank_line_before = false }
let spelling punctuation = punctuation_spelling punctuation
let opener_spelling bracket = spelling (Open bracket)
let closer_spelling bracket = spelling (Close bracket)

(* Where zero-width closers go when brackets are closed before a token: at
   the first line break before it, so that they come before the NEWLINE that
   may follow them and the tokens stay in order of position. *)
let closer_position first_line_break position =
  match first_line_break with Some (line_break : span) -> line_break.start | None -> position

let run ~source ~diagnostics ~mode pull =
  let output = Dynarray.create () in
  (* Open brackets, innermost first. *)
  let stack : (bracket * span) list ref = ref [] in
  let previous = ref None in
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
  (* Closes every open bracket at [position], reporting the innermost one with
     a fix that inserts [before ^ closers ^ after] at [fix_position]. *)
  let close_all ~position ~fix_position ~before ~after ~reason =
    match !stack with
    | [] -> ()
    | (innermost, innermost_span) :: outer ->
        let closers = String.concat "" (List.map (fun (bracket, _) -> closer_spelling bracket) !stack) in
        let notes =
          List.map
            (fun (bracket, span) ->
              (span, Printf.sprintf "This `%s` is not closed either." (opener_spelling bracket)))
            outer
        in
        report
          (Diagnostic.make ~code:Unclosed_bracket ~notes
             ~fixes:
               [
                 Diagnostic.fix
                   (Printf.sprintf "Insert `%s`" closers)
                   [ Diagnostic.insert fix_position (before ^ closers ^ after) ];
               ]
             innermost_span
             (Printf.sprintf "This `%s` is never closed%s." (opener_spelling innermost) reason));
        close_silently position
  in
  let close_bracket (current : Token.t) bracket =
    let span = current.span in
    if not (List.exists (fun (candidate, _) -> candidate = bracket) !stack) then
      report
        (Diagnostic.make ~code:Unmatched_closing_bracket span
           (Printf.sprintf "This `%s` has no `%s` to close." (closer_spelling bracket)
              (opener_spelling bracket)))
    else begin
      (* Openers above the match were never closed. *)
      let rec close_unclosed () =
        match !stack with
        | (top, _) :: _ when top = bracket -> ()
        | (unclosed, unclosed_span) :: _ ->
            let missing = closer_spelling unclosed in
            report
              (Diagnostic.make ~code:Unclosed_bracket
                 ~notes:
                   [
                     ( span,
                       Printf.sprintf "This `%s` closes an earlier `%s` first."
                         (closer_spelling bracket) (opener_spelling bracket) );
                   ]
                 ~fixes:
                   [
                     Diagnostic.fix (Printf.sprintf "Insert `%s`" missing)
                       [ Diagnostic.insert span.start missing ];
                   ]
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
  let finish (end_of_file : raw) =
    let position = end_of_file.raw_span.start in
    let text = Source.text source in
    (match (mode, !stack) with
    | _, [] -> ()
    | File { cut_off; _ }, _ :: _ when cut_off () ->
        close_silently (closer_position end_of_file.first_line_break position)
    | Interpolation { cut_off }, _ :: _ when cut_off () -> close_silently position
    | File _, _ :: _ ->
        let ends_with_line_break = position > 0 && (text.[position - 1] = '\n' || text.[position - 1] = '\r') in
        close_all
          ~position:(closer_position end_of_file.first_line_break position)
          ~fix_position:position
          ~before:(if ends_with_line_break || position = 0 then "" else "\n")
          ~after:(if ends_with_line_break then "\n" else "")
          ~reason:" before the end of the file"
    | Interpolation _, _ :: _ ->
        close_all ~position ~fix_position:position ~before:"" ~after:"" ~reason:" before the end of the interpolation");
    (match (mode, !previous) with
    | File _, Some previous_kind when can_end previous_kind ->
        emit
          (token Newline
             (match end_of_file.first_line_break with
             | Some span -> span
             | None -> Source.zero_width position))
    | _ -> ());
    emit
      {
        kind = End_of_file;
        span = end_of_file.raw_span;
        line_break_before = end_of_file.first_line_break <> None;
        blank_line_before = end_of_file.blank_line;
      };
    Dynarray.to_array output
  in
  let rec loop () =
    let raw = pull () in
    match raw.raw_kind with
    | End_of_file -> (
        match (mode, !stack) with
        | File { recovery = false; _ }, _ :: _ -> None
        | _ -> Some (finish raw))
    | kind ->
        let start = raw.raw_span.start in
        (match mode with
        | File { recovery = true; _ } when !stack <> [] && Token.starts_definition source start ->
            close_all
              ~position:(closer_position raw.first_line_break start)
              ~fix_position:start ~before:"" ~after:"\n" ~reason:" before the next definition"
        | _ -> ());
        let inside_parentheses =
          match !stack with ((Paren | Square), _) :: _ -> true | _ -> false
        in
        (match (raw.first_line_break, !previous) with
        | Some line_break, Some previous_kind
          when (not inside_parentheses) && can_end previous_kind && can_begin kind ->
            emit (token Newline line_break)
        | _ -> ());
        let current =
          {
            kind;
            span = raw.raw_span;
            line_break_before = raw.first_line_break <> None;
            blank_line_before = raw.blank_line;
          }
        in
        (match kind with
        | Punctuation (Open bracket) ->
            stack := (bracket, raw.raw_span) :: !stack;
            emit current
        | Punctuation (Close bracket) -> close_bracket current bracket
        | _ -> emit current);
        loop ()
  in
  loop ()

let file ~source ~diagnostics ~cut_off pull =
  match run ~source ~diagnostics ~mode:(File { recovery = false; cut_off }) pull with
  | Some tokens -> `Complete tokens
  | None -> `Unclosed_at_end

(* With recovery and in interpolations, open brackets are always closed, so
   [run] always returns tokens. *)
let file_with_recovery ~source ~diagnostics ~cut_off pull =
  Option.get (run ~source ~diagnostics ~mode:(File { recovery = true; cut_off }) pull)

let interpolation ~source ~diagnostics ~cut_off pull =
  Option.get (run ~source ~diagnostics ~mode:(Interpolation { cut_off }) pull)

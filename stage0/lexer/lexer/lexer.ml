(* The scanner and layout run as one pipeline. A file with brackets still
   open at its end is scanned twice, the second time with bracket recovery.

   A file's tokens are those of its text with its machine-applicable fixes
   applied, mapped back to its offsets, so it recovers as its fixes write.
   Its diagnostics are those of the text as written. *)

let attempt source ~recovery =
  let diagnostics = Diagnostic.Collector.create () in
  let scanner = Scanner.create source diagnostics in
  let tokens, open_at_end =
    Layout.file ~source ~diagnostics ~recovery (fun () -> Scanner.next scanner)
  in
  (tokens, Diagnostic.Collector.to_list diagnostics, open_at_end)

let scan source =
  match attempt source ~recovery:false with
  | tokens, diagnostics, false -> (tokens, diagnostics)
  | _, _, true ->
      let tokens, diagnostics, _ = attempt source ~recovery:true in
      (tokens, diagnostics)

let rec iter_names visit (tokens : Token.t array) =
  Array.iter
    (fun (token : Token.t) ->
      match token.kind with
      | Upper name | Lower name -> visit name
      | String literal ->
          Array.iter
            (fun (interpolation : Token.interpolation) -> iter_names visit interpolation.tokens)
            (Token.interpolations literal)
      | _ -> ())
    tokens

(* Withholds a rename to a spelling the file already has, or that two names
   share, which would make two names one. *)
let without_colliding_renames text (tokens : Token.t array) (diagnostics : Diagnostic.t list) =
  let written = Hashtbl.create 64 in
  iter_names (fun name -> Hashtbl.replace written name ()) tokens;
  let rename (diagnostic : Diagnostic.t) =
    match (diagnostic.code, diagnostic.fixes) with
    | Lexer Name_case, [ { edits = [ edit ]; _ } ] ->
        let span = diagnostic.span in
        Some (String.sub text span.start (span.stop - span.start), edit.replacement)
    | _ -> None
  in
  let renames = List.filter_map rename diagnostics in
  let collides (spelling, renamed) =
    Hashtbl.mem written renamed
    || List.exists (fun (other, again) -> again = renamed && other <> spelling) renames
  in
  List.map
    (fun (diagnostic : Diagnostic.t) ->
      match rename diagnostic with
      | Some rename when collides rename -> { diagnostic with fixes = [] }
      | _ -> diagnostic)
    diagnostics

type placed = { original : Source.span; fixed_start : int; fixed_stop : int }

let placed_edits (edits : Diagnostic.span Diagnostic.edit list) =
  let sorted =
    List.stable_sort
      (fun (left : Diagnostic.span Diagnostic.edit) right ->
        compare left.span.start right.span.start)
      edits
  in
  let _, placed =
    List.fold_left
      (fun (shift, placed) (edit : Diagnostic.span Diagnostic.edit) ->
        let fixed_start = edit.span.start + shift in
        let fixed_stop = fixed_start + String.length edit.replacement in
        ( shift + String.length edit.replacement - (edit.span.stop - edit.span.start),
          { original = edit.span; fixed_start; fixed_stop } :: placed ))
      (0, []) sorted
  in
  Array.of_list (List.rev placed)

(* The offset in the file of [offset] in the fixed text. Text an edit wrote
   maps to the text it replaced. *)
let original_offset (placed : placed array) ~is_stop offset =
  let starts_before (edit : placed) =
    if is_stop then edit.fixed_start < offset else edit.fixed_start <= offset
  in
  let rec search low high =
    if low >= high then low
    else
      let middle = (low + high) / 2 in
      if starts_before placed.(middle) then search (middle + 1) high else search low middle
  in
  match search 0 (Array.length placed) with
  | 0 -> offset
  | count ->
      let edit = placed.(count - 1) in
      if offset >= edit.fixed_stop then offset - edit.fixed_stop + edit.original.stop
      else if is_stop then edit.original.stop
      else edit.original.start

let rec original_token placed (token : Token.t) =
  (* A zero-width span maps as a stop, to stay inside a span ending there. *)
  let span (span : Source.span) =
    let stop = original_offset placed ~is_stop:true span.stop in
    if span.start = span.stop then Source.zero_width stop
    else Source.span (original_offset placed ~is_stop:false span.start) stop
  in
  let kind : Token.kind =
    match token.kind with
    | String literal ->
        let text (piece : Token.text) = { piece with span = span piece.span } in
        String
          {
            literal with
            tag = Option.map (fun (tag, tag_span) -> (tag, span tag_span)) literal.tag;
            first = text literal.first;
            rest =
              Array.map
                (fun ((interpolation : Token.interpolation), piece) ->
                  ( {
                      Token.tokens = Array.map (original_token placed) interpolation.tokens;
                      span = span interpolation.span;
                    },
                    text piece ))
                literal.rest;
          }
    | kind -> kind
  in
  { token with kind; span = span token.span }

(* The tokens of [fixed] that overlap two or more of [written]. *)
let rec joined ~(written : Token.t array) ~(fixed : Token.t array) =
  let tokens array =
    List.filter
      (fun (token : Token.t) ->
        token.kind <> Newline && token.kind <> End_of_file && token.span.start < token.span.stop)
      (Array.to_list array)
  in
  let inside (token : Token.t) =
    match token.kind with
    | String literal ->
        Array.concat
          (Array.to_list
             (Array.map
                (fun (interpolation : Token.interpolation) -> interpolation.tokens)
                (Token.interpolations literal)))
    | _ -> [||]
  in
  let rec walk (written : Token.t list) (fixed : Token.t list) =
    match fixed with
    | [] -> []
    | token :: rest -> (
        let rec after = function
          | (other : Token.t) :: others when other.span.stop <= token.span.start -> after others
          | written -> written
        in
        let written = after written in
        let overlaps (other : Token.t) = other.span.start < token.span.stop in
        match written with
        | first :: second :: _ when overlaps first && overlaps second ->
            token.span :: walk written rest
        | first :: _ when overlaps first ->
            joined ~written:(inside first) ~fixed:(inside token) @ walk written rest
        | _ -> walk written rest)
  in
  walk (tokens written) (tokens fixed)

(* The tokens of the text with [fixes] applied, each a diagnostic's fix, if
   that text adds no error and joins or splits no neighboring token. *)
let works source tokens diagnostics fixes =
  let edits =
    List.concat_map (fun (_, (fix : Diagnostic.span Diagnostic.fix)) -> fix.edits) fixes
  in
  let fixed_tokens, remaining =
    scan
      (Source.create ~path:(Source.path source) (Diagnostic.apply_edits (Source.text source) edits))
  in
  let fixed_tokens = Array.map (original_token (placed_edits edits)) fixed_tokens in
  let others =
    List.filter
      (fun diagnostic -> not (List.exists (fun (fixed, _) -> fixed == diagnostic) fixes))
      diagnostics
  in
  match joined ~written:tokens ~fixed:fixed_tokens @ joined ~written:fixed_tokens ~fixed:tokens with
  | [] when Diagnostic.adds_none ~before:others ~after:remaining -> Some fixed_tokens
  | _ -> None

(* A fix that joins or splits a neighboring token, or adds an error, is
   withheld, and the file is lexed again without it. *)
let rec recover source tokens diagnostics =
  let fixes =
    List.filter_map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with [ fix ] -> Some (diagnostic, fix) | _ -> None)
      (Diagnostic.machine_applicable diagnostics)
  in
  match fixes with
  | [] -> (tokens, diagnostics)
  | _ -> (
      let withhold wrong =
        recover source tokens
          (List.map
             (fun (diagnostic : Diagnostic.t) ->
               if List.exists (fun (fixed, _) -> fixed == diagnostic) wrong then
                 { diagnostic with fixes = [] }
               else diagnostic)
             diagnostics)
      in
      match works source tokens diagnostics fixes with
      | Some fixed_tokens -> (
          (* A fix may work only with another, as `..<` fixed to `..` before
             `.0` does; each must work alone too. *)
          match fixes with
          | [ _ ] -> (fixed_tokens, diagnostics)
          | _ -> (
              match
                List.filter
                  (fun fix -> Option.is_none (works source tokens diagnostics [ fix ]))
                  fixes
              with
              | [] -> (fixed_tokens, diagnostics)
              | wrong -> withhold wrong))
      | None ->
          (* Each fix that breaks the ones before it. *)
          let wrong =
            snd
              (List.fold_left
                 (fun (accepted, wrong) fix ->
                   if Option.is_some (works source tokens diagnostics (fix :: accepted)) then
                     (fix :: accepted, wrong)
                   else (accepted, fix :: wrong))
                 ([], []) fixes)
          in
          if wrong = [] then (tokens, diagnostics) else withhold wrong)

(* A diagnostic's alternative fixes, which recovery does not apply, are
   each checked alone. One left alone would be applied without review, so
   fewer than two leave none. *)
let with_working_alternatives source tokens diagnostics =
  List.map
    (fun (diagnostic : Diagnostic.t) ->
      match diagnostic.fixes with
      | _ :: _ :: _ -> (
          match
            List.filter
              (fun fix -> Option.is_some (works source tokens diagnostics [ (diagnostic, fix) ]))
              diagnostic.fixes
          with
          | _ :: _ :: _ as fixes -> { diagnostic with fixes }
          | _ -> { diagnostic with fixes = [] })
      | _ -> diagnostic)
    diagnostics

let lex source =
  let tokens, diagnostics = scan source in
  let diagnostics =
    with_working_alternatives source tokens
      (without_colliding_renames (Source.text source) tokens diagnostics)
  in
  recover source tokens diagnostics

module For_testing = struct
  let can_end = Layout.can_end
  let can_begin = Layout.can_begin
end

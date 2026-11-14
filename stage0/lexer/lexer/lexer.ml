(* The scanner and layout run as one pipeline: layout requests each raw
   token from the scanner when it needs it. A file with brackets still open
   at its end is scanned twice, the second time with bracket recovery
   enabled.

   A file with errors is then lexed again with its machine-applicable fixes
   applied, and the tokens of that fixed text, mapped back to the file's
   offsets, are the file's tokens. The lexer therefore recovers from each
   such error exactly as its fix writes, by construction: the parser reads
   the tokens of the program the fixes make, with their values, line breaks,
   and indentation. The diagnostics are those of the file as written. If the
   fixed text has a diagnostic the file does not, a fix was wrong, and the
   tokens of the file as written are kept instead. *)

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

(* Calls [visit] on every name token, inside interpolations too. *)
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

(* A fix that renames a name to the case rules is withheld when the new
   spelling is already a name in the file, or when two spellings would both
   become it: applying it would make two names one, and change what a use
   refers to. A name of another file that this file does not write is not
   seen here. *)
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
  let sources = Hashtbl.create 16 in
  List.iter
    (fun diagnostic ->
      match rename diagnostic with
      | Some (spelling, renamed) ->
          let spellings = Option.value (Hashtbl.find_opt sources renamed) ~default:[] in
          if not (List.mem spelling spellings) then
            Hashtbl.replace sources renamed (spelling :: spellings)
      | None -> ())
    diagnostics;
  List.map
    (fun (diagnostic : Diagnostic.t) ->
      match rename diagnostic with
      | Some (_, renamed)
        when Hashtbl.mem written renamed || List.length (Hashtbl.find sources renamed) > 1 ->
          { diagnostic with fixes = [] }
      | _ -> diagnostic)
    diagnostics

(* An edit in both texts: [original] in the file, and [fixed] where its
   replacement lies in the fixed text. *)
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
   maps to the text it replaced: a token's start to the replaced text's
   start, and its stop to the replaced text's stop, so a token an edit wrote
   whole, such as a closer it inserted, spans the text it replaced and is
   zero-width where it was inserted. *)
let original_offset (placed : placed array) ~is_stop offset =
  (* The last edit whose replacement starts at or before [offset], or, for a
     stop, strictly before it, so that a stop at an edit's start maps by the
     text before the edit. *)
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
  (* A zero-width span, such as the end of the file after a deleted `;`,
     stays zero-width, at the place a stop there maps to: before deleted
     text, so that it stays inside a span that ends at the same place. *)
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

let lex source =
  let tokens, diagnostics = scan source in
  let diagnostics = without_colliding_renames (Source.text source) tokens diagnostics in
  match Diagnostic.machine_applicable diagnostics with
  | [] -> (tokens, diagnostics)
  | applied ->
      let edits =
        List.concat_map
          (fun (diagnostic : Diagnostic.t) ->
            match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
          applied
      in
      let fixed_tokens, remaining =
        scan
          (Source.create ~path:(Source.path source)
             (Diagnostic.apply_edits (Source.text source) edits))
      in
      let others = List.filter (fun diagnostic -> not (List.memq diagnostic applied)) diagnostics in
      if Diagnostic.adds_none ~before:others ~after:remaining then
        (Array.map (original_token (placed_edits edits)) fixed_tokens, diagnostics)
      else (tokens, diagnostics)

module For_testing = struct
  let can_end = Layout.can_end
  let can_begin = Layout.can_begin
end

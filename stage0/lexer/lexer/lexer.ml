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

let placed_edits (edits : Source.span Diagnostic.edit list) =
  let sorted =
    List.stable_sort
      (fun (left : Source.span Diagnostic.edit) right -> compare left.span.start right.span.start)
      edits
  in
  let _, placed =
    List.fold_left
      (fun (shift, placed) (edit : Source.span Diagnostic.edit) ->
        let fixed_start = edit.span.start + shift in
        let fixed_stop = fixed_start + String.length edit.replacement in
        ( shift + String.length edit.replacement - (edit.span.stop - edit.span.start),
          { original = edit.span; fixed_start; fixed_stop } :: placed ))
      (0, []) sorted
  in
  Array.of_list (List.rev placed)

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
                      interpolation with
                      tokens = Array.map (original_token placed) interpolation.tokens;
                      span = span interpolation.span;
                    },
                    text piece ))
                literal.rest;
          }
    | kind -> kind
  in
  { token with kind; span = span token.span }

let to_original edits tokens = Array.map (original_token (placed_edits edits)) tokens

let rec with_inserted_closers_marked (tokens : Token.t array) =
  Array.map
    (fun (token : Token.t) ->
      match token.kind with
      | Punctuation (Close _) when token.span.start = token.span.stop ->
          { token with is_inserted_closer = true }
      | String literal ->
          {
            token with
            kind =
              String
                {
                  literal with
                  rest =
                    Array.map
                      (fun ((interpolation : Token.interpolation), text) ->
                        ( {
                            interpolation with
                            tokens = with_inserted_closers_marked interpolation.tokens;
                          },
                          text ))
                      literal.rest;
                };
          }
      | _ -> token)
    tokens

let lex source =
  let tokens, diagnostics = scan source in
  let diagnostics = without_colliding_renames (Source.text source) tokens diagnostics in
  let edits =
    List.concat_map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with [ fix ] -> fix.edits | _ -> [])
      (Diagnostic.machine_applicable diagnostics)
  in
  match edits with
  | [] -> (with_inserted_closers_marked tokens, diagnostics)
  | _ ->
      let fixed_tokens, _ =
        scan
          (Source.create ~path:(Source.path source)
             (Diagnostic.apply_edits (Source.text source) edits))
      in
      (with_inserted_closers_marked (to_original edits fixed_tokens), diagnostics)

module For_testing = struct
  let scan = scan
  let to_original = to_original
end

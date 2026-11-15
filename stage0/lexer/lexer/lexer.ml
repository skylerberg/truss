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
                      Token.tokens = Array.map (original_token placed) interpolation.tokens;
                      span = span interpolation.span;
                    },
                    text piece ))
                literal.rest;
          }
    | kind -> kind
  in
  { token with kind; span = span token.span }

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

let membership fixes =
  let table = Hashtbl.create 64 in
  List.iter
    (fun (((diagnostic : Diagnostic.t), _) as fix) ->
      Hashtbl.add table (diagnostic.span.start, diagnostic.span.stop) fix)
    fixes;
  fun (diagnostic : Diagnostic.t) fix ->
    List.exists
      (fun (other_diagnostic, other_fix) -> other_diagnostic == diagnostic && other_fix == fix)
      (Hashtbl.find_all table (diagnostic.span.start, diagnostic.span.stop))

let works source tokens diagnostics fixes =
  let edits =
    List.concat_map (fun (_, (fix : Diagnostic.span Diagnostic.fix)) -> fix.edits) fixes
  in
  let fixed_tokens, remaining =
    scan
      (Source.create ~path:(Source.path source) (Diagnostic.apply_edits (Source.text source) edits))
  in
  let fixed_tokens = Array.map (original_token (placed_edits edits)) fixed_tokens in
  let is_fixed = membership fixes in
  let others =
    List.filter
      (fun (diagnostic : Diagnostic.t) -> not (List.exists (is_fixed diagnostic) diagnostic.fixes))
      diagnostics
  in
  match joined ~written:tokens ~fixed:fixed_tokens @ joined ~written:fixed_tokens ~fixed:tokens with
  | [] when Diagnostic.adds_none ~before:others ~after:remaining -> Some fixed_tokens
  | _ -> None

let extent ((_, fix) : Diagnostic.t * Diagnostic.span Diagnostic.fix) =
  List.fold_left
    (fun (start, stop) (edit : Diagnostic.span Diagnostic.edit) ->
      (min start edit.span.start, max stop edit.span.stop))
    (max_int, min_int) fix.edits

let first_index count predicate =
  let rec search low high =
    if low >= high then low
    else
      let middle = (low + high) / 2 in
      if predicate middle then search low middle else search (middle + 1) high
  in
  search 0 count

let widened (spans : Source.span array) (start, stop) =
  let count = Array.length spans in
  let before = first_index count (fun index -> spans.(index).start >= start) - 1 in
  let after = first_index count (fun index -> spans.(index).stop > stop) in
  ( (if before >= 0 then min start spans.(before).start else start),
    if after < count then max stop spans.(after).stop else stop )

let clusters (tokens : Token.t array) fixes =
  let spans =
    Array.of_list
      (List.filter_map
         (fun (token : Token.t) ->
           if token.span.start < token.span.stop then Some token.span else None)
         (Array.to_list tokens))
  in
  let regions =
    List.stable_sort
      (fun ((left_start, _), _) ((right_start, _), _) -> compare left_start right_start)
      (List.map (fun fix -> (widened spans (extent fix), fix)) fixes)
  in
  let finished, current, _ =
    List.fold_left
      (fun (finished, current, current_stop) ((start, stop), fix) ->
        match current with
        | _ :: _ when start < current_stop -> (finished, fix :: current, max stop current_stop)
        | [] -> (finished, [ fix ], stop)
        | _ -> (List.rev current :: finished, [ fix ], stop))
      ([], [], min_int) regions
  in
  List.rev (match current with [] -> finished | _ -> List.rev current :: finished)

let rec failing source tokens diagnostics ~fixes_of groups =
  match groups with
  | [] -> []
  | _ when Option.is_some (works source tokens diagnostics (List.concat_map fixes_of groups)) -> []
  | [ group ] -> [ group ]
  | _ ->
      let half = List.length groups / 2 in
      failing source tokens diagnostics ~fixes_of
        (List.filteri (fun index _ -> index < half) groups)
      @ failing source tokens diagnostics ~fixes_of
          (List.filteri (fun index _ -> index >= half) groups)

let largest_checked_cluster = 8

let accepted source tokens diagnostics ~combines fixes =
  let clusters =
    Array.of_list
      (List.map Array.of_list
         (List.filter
            (fun cluster -> List.length cluster <= largest_checked_cluster)
            (clusters tokens fixes)))
  in
  let accepted = Array.make (Array.length clusters) [] in
  let rounds = Array.fold_left (fun most cluster -> max most (Array.length cluster)) 0 clusters in
  for round = 0 to rounds - 1 do
    let candidate index = clusters.(index).(round) in
    let candidates =
      List.filter
        (fun index -> round < Array.length clusters.(index))
        (List.init (Array.length clusters) Fun.id)
    in
    let rejected = Array.make (Array.length clusters) false in
    let reject = List.iter (fun index -> rejected.(index) <- true) in
    reject
      (failing source tokens diagnostics ~fixes_of:(fun index -> [ candidate index ]) candidates);
    if combines then
      reject
        (failing source tokens diagnostics
           ~fixes_of:(fun index -> candidate index :: accepted.(index))
           (List.filter (fun index -> (not rejected.(index)) && accepted.(index) <> []) candidates));
    List.iter
      (fun index ->
        if not rejected.(index) then accepted.(index) <- candidate index :: accepted.(index))
      candidates
  done;
  List.concat (Array.to_list accepted)

let recover source tokens diagnostics =
  let fixes =
    List.filter_map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with [ fix ] -> Some (diagnostic, fix) | _ -> None)
      (Diagnostic.machine_applicable diagnostics)
  in
  let applied = accepted source tokens diagnostics ~combines:true fixes in
  let is_applied = membership applied and is_offered = membership fixes in
  let diagnostics =
    List.map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with
        | [ fix ] when is_offered diagnostic fix && not (is_applied diagnostic fix) ->
            { diagnostic with fixes = [] }
        | _ -> diagnostic)
      diagnostics
  in
  match applied with
  | [] -> (tokens, diagnostics)
  | _ -> (
      match works source tokens diagnostics applied with
      | Some fixed_tokens -> (fixed_tokens, diagnostics)
      | None ->
          Compiler_bug.bug ~stage:"Lexer"
            "the fixes of %s that each work in their cluster fail together" (Source.path source))

let with_working_alternatives source tokens diagnostics =
  let alternatives =
    List.concat_map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with
        | _ :: _ :: _ -> List.map (fun fix -> (diagnostic, fix)) diagnostic.fixes
        | _ -> [])
      diagnostics
  in
  let works_alone = membership (accepted source tokens diagnostics ~combines:false alternatives) in
  List.map
    (fun (diagnostic : Diagnostic.t) ->
      match diagnostic.fixes with
      | _ :: _ :: _ -> (
          match List.filter (works_alone diagnostic) diagnostic.fixes with
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

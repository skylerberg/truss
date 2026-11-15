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

let rec joined ~(edits : Source.span Diagnostic.edit list) ~(written : Token.t array)
    ~(fixed : Token.t array) =
  let is_replaced (span : Source.span) =
    List.exists
      (fun (edit : Source.span Diagnostic.edit) ->
        edit.span.start < edit.span.stop && edit.span.start <= span.start
        && span.stop <= edit.span.stop)
      edits
  in
  let tokens ~is_kept array =
    List.filter
      (fun (token : Token.t) ->
        token.kind <> Newline && token.kind <> End_of_file
        && token.span.start < token.span.stop
        && is_kept token)
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
            joined ~edits ~written:(inside first) ~fixed:(inside token) @ walk written rest
        | _ -> walk written rest)
  in
  walk
    (tokens ~is_kept:(fun _ -> true) written)
    (tokens ~is_kept:(fun (token : Token.t) -> not (is_replaced token.span)) fixed)

let alters_neighbors ~edits ~written ~fixed =
  joined ~edits ~written ~fixed @ joined ~edits ~written:fixed ~fixed:written <> []

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

let extent ((_, fix) : Diagnostic.t * Source.span Diagnostic.fix) =
  List.fold_left
    (fun (start, stop) (edit : Source.span Diagnostic.edit) ->
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

let rec failing works ~fixes_of groups =
  match groups with
  | [] -> []
  | _ when Option.is_some (works (List.concat_map fixes_of groups)) -> []
  | [ group ] -> [ group ]
  | _ ->
      let half = List.length groups / 2 in
      failing works ~fixes_of (List.filteri (fun index _ -> index < half) groups)
      @ failing works ~fixes_of (List.filteri (fun index _ -> index >= half) groups)

let largest_checked_cluster = 8

let accepted works tokens ~combines fixes =
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
    reject (failing works ~fixes_of:(fun index -> [ candidate index ]) candidates);
    if combines then
      reject
        (failing works
           ~fixes_of:(fun index -> candidate index :: accepted.(index))
           (List.filter (fun index -> (not rejected.(index)) && accepted.(index) <> []) candidates));
    List.iter
      (fun index ->
        if not rejected.(index) then accepted.(index) <- candidate index :: accepted.(index))
      candidates
  done;
  List.concat (Array.to_list accepted)

let recover ~stage ~path ~attempt ~is_applied tokens (diagnostics : Diagnostic.t list) =
  let works fixes =
    let is_fixed = membership fixes in
    let unfixed =
      List.filter
        (fun (diagnostic : Diagnostic.t) ->
          not (List.exists (is_fixed diagnostic) diagnostic.fixes))
        diagnostics
    in
    attempt
      (List.concat_map (fun (_, (fix : Source.span Diagnostic.fix)) -> fix.edits) fixes)
      ~unfixed
  in
  let is_checked_alone (diagnostic : Diagnostic.t) =
    match diagnostic.fixes with
    | _ :: _ :: _ -> true
    | [ _ ] -> not (is_applied diagnostic)
    | [] -> false
  in
  let works_alone =
    membership
      (accepted works tokens ~combines:false
         (List.concat_map
            (fun (diagnostic : Diagnostic.t) ->
              if is_checked_alone diagnostic then
                List.map (fun fix -> (diagnostic, fix)) diagnostic.fixes
              else [])
            diagnostics))
  in
  let diagnostics =
    List.map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with
        | _ :: _ :: _ -> (
            match List.filter (works_alone diagnostic) diagnostic.fixes with
            | _ :: _ :: _ as fixes -> { diagnostic with fixes }
            | _ -> { diagnostic with fixes = [] })
        | [ fix ] when is_checked_alone diagnostic && not (works_alone diagnostic fix) ->
            { diagnostic with fixes = [] }
        | _ -> diagnostic)
      diagnostics
  in
  let fixes =
    List.filter_map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with
        | [ fix ] when is_applied diagnostic -> Some (diagnostic, fix)
        | _ -> None)
      (Diagnostic.machine_applicable diagnostics)
  in
  let applied = accepted works tokens ~combines:true fixes in
  let is_applied_fix = membership applied and is_offered = membership fixes in
  let diagnostics =
    List.map
      (fun (diagnostic : Diagnostic.t) ->
        match diagnostic.fixes with
        | [ fix ] when is_offered diagnostic fix && not (is_applied_fix diagnostic fix) ->
            { diagnostic with fixes = [] }
        | _ -> diagnostic)
      diagnostics
  in
  match applied with
  | [] -> (diagnostics, None)
  | _ -> (
      match works applied with
      | Some fixed -> (diagnostics, Some fixed)
      | None ->
          Compiler_bug.bug ~stage "the fixes of %s that each work in their cluster fail together"
            path)

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
  let attempt edits ~unfixed =
    let fixed_tokens, remaining =
      scan
        (Source.create ~path:(Source.path source)
           (Diagnostic.apply_edits (Source.text source) edits))
    in
    let fixed_tokens = Fixes.to_original edits fixed_tokens in
    if
      Fixes.alters_neighbors ~edits ~written:tokens ~fixed:fixed_tokens
      || not (Diagnostic.adds_none ~before:unfixed ~after:remaining)
    then None
    else Some fixed_tokens
  in
  let diagnostics, fixed =
    Fixes.apply ~stage:"Lexer" ~path:(Source.path source) ~attempt
      ~is_applied:(fun _ -> true)
      tokens
      (without_colliding_renames (Source.text source) tokens diagnostics)
  in
  (with_inserted_closers_marked (Option.value fixed ~default:tokens), diagnostics)

module For_testing = struct
  let can_end = Layout.can_end
  let can_begin = Layout.can_begin
end

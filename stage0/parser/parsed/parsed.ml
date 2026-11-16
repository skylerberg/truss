type t = { file : Syntax.file; diagnostics : Diagnostic.t list; text : string }

let parse source =
  let tokens, lexer_diagnostics = Lexer.lex source in
  let file, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
  let attempt edits ~unfixed =
    let fixed_tokens, fixed_lexer_diagnostics =
      Lexer.lex
        (Source.create ~path:(Source.path source)
           (Diagnostic.apply_edits (Source.text source) edits))
    in
    let fixed_tokens = Fixes.to_original edits fixed_tokens in
    if Fixes.alters_neighbors ~edits ~written:tokens ~fixed:fixed_tokens then None
    else
      let _, fixed_parser_diagnostics = Parser.parse fixed_tokens ~lexer_diagnostics:[] in
      if
        Diagnostic.adds_none ~before:(lexer_diagnostics @ unfixed)
          ~after:(fixed_lexer_diagnostics @ fixed_parser_diagnostics)
      then Some ()
      else None
  in
  let parser_diagnostics, _ =
    Fixes.apply ~stage:"Parser" ~path:(Source.path source) ~attempt
      ~is_applied:(fun _ -> false)
      tokens parser_diagnostics
  in
  { file; diagnostics = lexer_diagnostics @ parser_diagnostics; text = Source.text source }

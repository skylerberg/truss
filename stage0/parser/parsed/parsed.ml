type t = { file : Syntax.file; diagnostics : Diagnostic.t list; text : string }

let is_recovery (diagnostic : Diagnostic.t) =
  match diagnostic.code with Parser code -> Parser.recovers code | _ -> false

let parse source =
  let tokens, lexer_diagnostics = Lexer.lex source in
  let written, parser_diagnostics = Parser.parse tokens in
  let attempt edits ~unfixed =
    let fixed_tokens, fixed_lexer_diagnostics =
      Lexer.lex
        (Source.create ~path:(Source.path source)
           (Diagnostic.apply_edits (Source.text source) edits))
    in
    let fixed_tokens = Lexer.Recovery.to_original edits fixed_tokens in
    if Lexer.Recovery.alters_neighbors ~edits ~written:tokens ~fixed:fixed_tokens then None
    else
      let fixed, fixed_parser_diagnostics = Parser.parse fixed_tokens in
      if
        Diagnostic.adds_none ~before:(lexer_diagnostics @ unfixed)
          ~after:(fixed_lexer_diagnostics @ fixed_parser_diagnostics)
      then Some fixed
      else None
  in
  let parser_diagnostics, fixed =
    Lexer.Recovery.recover ~stage:"Parser" ~path:(Source.path source) ~attempt
      ~is_applied:is_recovery tokens parser_diagnostics
  in
  {
    file = Option.value fixed ~default:written;
    diagnostics = lexer_diagnostics @ parser_diagnostics;
    text = Source.text source;
  }

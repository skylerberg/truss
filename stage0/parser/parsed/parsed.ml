type file = {
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

let file =
  Query.query ~name:"file" ~phase:Phases.syntax ~show:Path.show_file (fun database file ->
      let source = Query.demand database Packages.source file in
      let tokens, lexer_diagnostics = Lexer.lex source in
      let parsed, parser_diagnostics = Parser.parse source tokens in
      {
        uses = parsed.uses;
        definitions = parsed.definitions;
        diagnostics = lexer_diagnostics @ parser_diagnostics;
      })

type file = {
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

let parse source =
  let tokens, lexer_diagnostics = Lexer.lex source in
  let parsed, parser_diagnostics = Parser.parse source tokens in
  {
    uses = parsed.uses;
    definitions = parsed.definitions;
    diagnostics = lexer_diagnostics @ parser_diagnostics;
  }

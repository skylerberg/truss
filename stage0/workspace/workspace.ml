type dependency = { package : string; capabilities : string list }
type package = { name : string; dependencies : dependency list; modules : Path.module_ list }

let packages : (string, package) Query.input = Query.input ~name:"package" ~show:Fun.id ()

let file_text : (Path.module_, string) Query.input =
  Query.input ~name:"file_text" ~show:Path.show_module ()

let file_path (module_ : Path.module_) =
  String.concat "/" (module_.package :: module_.modules) ^ ".truss"

type file = {
  source : Source.t;
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

(* A file's [Source.t] holds a table of lines, which equality compares as
   it would anything else; two parses of the same text give equal files. *)
let file =
  Query.query ~name:"file" ~show:Path.show_module (fun database module_ ->
      let text = Query.get database file_text module_ in
      let source = Source.create ~path:(file_path module_) text in
      let tokens, lexer_diagnostics = Lexer.lex source in
      let parsed, parser_diagnostics = Parser.parse source tokens in
      {
        source;
        uses = parsed.uses;
        definitions = parsed.definitions;
        diagnostics = lexer_diagnostics @ parser_diagnostics;
      })

let package database name = Query.find database packages name

let module_exists =
  Query.query ~name:"module_exists" ~show:Path.show_module (fun database (module_ : Path.module_) ->
      match package database module_.package with
      | None -> false
      | Some package -> List.mem module_ package.modules)

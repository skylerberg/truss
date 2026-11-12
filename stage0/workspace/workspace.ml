let file_path (module_ : Path.module_) = String.concat "/" (Path.module_parts module_) ^ ".truss"

type file = {
  source : Source.t;
  tokens : Token.t array;
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

(* A file's [Source.t] holds a table of lines, which equality compares as
   it would anything else; two parses of the same text give equal files. *)
let file =
  Query.query ~name:"file" ~phase:Phases.syntax ~show:Path.show_module (fun database module_ ->
      let text =
        match Query.demand database Project.module_text module_ with
        | Some text -> text
        | None -> raise Not_found
      in
      let source = Source.create ~path:(file_path module_) text in
      let tokens, lexer_diagnostics = Lexer.lex source in
      let parsed, parser_diagnostics = Parser.parse source tokens in
      {
        source;
        tokens;
        uses = parsed.uses;
        definitions = parsed.definitions;
        diagnostics = lexer_diagnostics @ parser_diagnostics;
      })

let package database name = Query.demand database Project.package name

(* What a package's manifest says, one thing at a time: a result that reads
   only a package's modules is not worked out again when its dependencies
   change, and the other way round. *)
let modules =
  Query.query ~name:"package_modules" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.modules | None -> [])

let dependencies =
  Query.query ~name:"package_dependencies" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.dependencies | None -> [])

let usize_bits =
  Query.query ~name:"package_usize_bits" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.usize_bits | None -> 32)

let exists =
  Query.query ~name:"package_exists" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name -> Option.is_some (package database name))

let split_module database names = Path.split_module ~is_package:(Query.demand database exists) names

let module_exists =
  Query.query ~name:"module_exists" ~phase:Phases.syntax ~saved:true ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      List.mem module_ (Query.demand database modules module_.package))

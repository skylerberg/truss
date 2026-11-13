type file = {
  source : Source.t;
  uses : Syntax.path Syntax.item list;
  definitions : Syntax.definition Syntax.item list;
  diagnostics : Diagnostic.t list;
}

(* A file's [Source.t] holds a table of lines, which equality compares as
   it would anything else; two parses of the same text give equal files. *)
let file =
  Query.query ~name:"file" ~phase:Phases.syntax ~show:Path.show_file (fun database file ->
      let text =
        match Query.demand database Project.file_text file with
        | Some text -> text
        | None -> raise Not_found
      in
      let source = Source.create ~path:(Path.show_file file) text in
      let tokens, lexer_diagnostics = Lexer.lex source in
      let parsed, parser_diagnostics = Parser.parse source tokens in
      {
        source;
        uses = parsed.uses;
        definitions = parsed.definitions;
        diagnostics = lexer_diagnostics @ parser_diagnostics;
      })

let package database name = Query.demand database Project.package name

(* A package's manifest, one field at a time: a result that reads
   only a package's modules is not recomputed when its dependencies
   change, and the other way round. *)
let modules =
  Query.query ~name:"package_modules" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.modules | None -> [])

(* A module's files, in order. Every file of a package is in a module, so a
   module that has no file is not one. *)
let package_files =
  Query.query ~name:"package_files" ~phase:Phases.syntax ~show:Path.show_package
    (fun database name ->
      match package database name with Some package -> package.files | None -> [])

let files =
  Query.query ~name:"module_files" ~phase:Phases.syntax ~show:Path.show_module
    (fun database (module_ : Path.module_) ->
      List.filter
        (fun (file : Path.file) -> file.module_ = module_)
        (Query.demand database package_files module_.package))

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

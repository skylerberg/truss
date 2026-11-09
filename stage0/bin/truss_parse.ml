(* truss-parse [--json] [--tree] FILE

   Lexes and parses one file and prints its diagnostics, for people or, with
   --json, for tools. With --tree it also prints each definition's syntax
   tree as an S-expression. Exits with status 1 if there are diagnostics. *)

let () =
  let json = ref false and show_tree = ref false and files = ref [] in
  Arg.parse
    [
      ("--json", Arg.Set json, " Print diagnostics as JSON");
      ("--tree", Arg.Set show_tree, " Print the syntax tree too");
    ]
    (fun file -> files := file :: !files)
    "truss-parse [--json] [--tree] FILE";
  match !files with
  | [ file ] ->
      let source = Source.read_file file in
      let tokens, lexer_diagnostics = Lexer.lex source in
      let tree, parser_diagnostics = Parser.parse source tokens in
      let diagnostics =
        List.stable_sort
          (fun (a : Diagnostic.t) (b : Diagnostic.t) -> compare a.span.start b.span.start)
          (lexer_diagnostics @ parser_diagnostics)
      in
      if !show_tree then print_endline (Syntax_print.file tree);
      let shown = Diagnostic.shown diagnostics in
      if !json then print_string (Diagnostic.to_json source shown)
      else List.iter (fun diagnostic -> print_string (Diagnostic.render source diagnostic)) shown;
      exit (if diagnostics = [] then 0 else 1)
  | _ ->
      prerr_endline "truss-parse: expected one file";
      exit 2

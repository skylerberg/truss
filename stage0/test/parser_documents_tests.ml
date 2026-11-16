let () =
  Harness.test "SPECIFICATION.md lists the words the parser recognizes by spelling" (fun () ->
      let listed =
        Documents.words
          (Documents.block_after
             (Parse_support.document "SPECIFICATION.md")
             "name resolution gives the rest their meaning")
      in
      let missing =
        List.filter (fun word -> not (List.mem word listed)) Parser.For_testing.contextual_keywords
      in
      if missing <> [] then Harness.fail "not listed: %s" (String.concat ", " missing));
  Harness.test "SPECIFICATION.md lists every conflict that a precedence declaration resolves"
    (fun () ->
      let rec section = function
        | [] -> []
        | "## Ambiguities in the grammar" :: rest -> rest
        | _ :: rest -> section rest
      in
      let rec entries count = function
        | line :: rest when not (String.starts_with ~prefix:"#" line) ->
            entries (if String.starts_with ~prefix:"- " line then count + 1 else count) rest
        | _ -> count
      in
      let listed =
        entries 0 (section (String.split_on_char '\n' (Parse_support.document "SPECIFICATION.md")))
      in
      if listed <> Reference_parser.conflicts_resolved_by_precedence then
        Harness.fail
          "Menhir resolves %d conflicts by precedence, and \"Ambiguities in the grammar\" lists %d"
          Reference_parser.conflicts_resolved_by_precedence listed)

let markdown_files = Harness.markdown_documents ()

let snippet text =
  let source = Parse_support.source text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let items, parser_diagnostics = Reference_parser.Snippet.parse tokens in
  (tokens, items, lexer_diagnostics @ parser_diagnostics)

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          Harness.test
            (Printf.sprintf "%s block %d parses cleanly" name (index + 1))
            (fun () ->
              let _, _, diagnostics = snippet text in
              Parse_support.no_diagnostics text diagnostics))
        (Documents.truss_blocks (Parse_support.document name)))
    markdown_files

let () =
  Harness.test "a signature without a body in an example is checked" (fun () ->
      let _, _, diagnostics = snippet "fn f(x: Int64)\n  requires x & 1 < 2" in
      if Parse_support.codes diagnostics <> [ "parser.needs_parentheses" ] then
        Harness.fail "got [%s]" (String.concat "; " (Parse_support.codes diagnostics)))

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          Harness.test
            (Printf.sprintf "%s block %d is accepted by the grammar" name (index + 1))
            (fun () ->
              let tokens, items, _ = snippet text in
              List.iter
                (fun (item : Reference_parser.Snippet.item) ->
                  let slice =
                    Array.to_list (Array.sub tokens item.first (item.stop - item.first))
                  in
                  if not (Reference_parser.accepts (Reference_parser.Snippet.entry item.kind) slice)
                  then
                    Harness.fail "the grammar rejects tokens %d to %d of %S" item.first item.stop
                      text)
                items))
        (Documents.truss_blocks (Parse_support.document name)))
    markdown_files

let () =
  Harness.test "the grammar accepts every Truss file of the repository that the parser accepts"
    (fun () ->
      List.iter
        (fun path ->
          let source =
            Source.create ~path
              (In_channel.with_open_bin (Harness.workspace_path path) In_channel.input_all)
          in
          let tokens, lexer_diagnostics = Lexer.lex source in
          let _, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
          if
            lexer_diagnostics = [] && parser_diagnostics = []
            && not (Reference_parser.accepts Reference_parser.file (Array.to_list tokens))
          then Harness.fail "the grammar rejects %s" path)
        (Harness.truss_files ()));
  Harness.test "the grammar rejects every input the parser rejects" (fun () ->
      List.iter
        (fun text ->
          let tokens, _ = Lexer.lex (Parse_support.source text) in
          if Reference_parser.accepts Reference_parser.file (Array.to_list tokens) then
            Harness.fail "accepted %S" text)
        [
          "fn f() { a & b == c }\n";
          "fn f() { a && b || c }\n";
          "fn f() { x = 0.. }\n";
          "type T = | \n";
        ])

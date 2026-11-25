let () =
  Harness.test "SPECIFICATION.md's table of words that are not reserved lists the parser's"
    (fun () ->
      let rec skip_to_table = function
        | [] -> []
        | line :: rest ->
            if String.starts_with ~prefix:"| Words |" line then take_rows rest
            else skip_to_table rest
      and take_rows = function
        | line :: rest when String.starts_with ~prefix:"|" line -> line :: take_rows rest
        | _ -> []
      in
      let rows =
        skip_to_table (String.split_on_char '\n' (Parse_support.read_document "SPECIFICATION.md"))
      in
      let missing =
        List.filter
          (fun word ->
            not (List.exists (fun row -> String.includes ~affix:("`" ^ word ^ "`") row) rows))
          Parser.For_testing.contextual_keywords
      in
      if missing <> [] then Harness.fail "not listed: %s" (String.concat ", " missing));
  Harness.test "Menhir resolves the grammar's three known conflicts by precedence, and no other"
    (fun () ->
      let known_conflicts = 3 in
      if Reference_parser.conflicts_resolved_by_precedence <> known_conflicts then
        Harness.fail
          "Menhir resolves %d conflicts by precedence, not %d. State how each new conflict \
           resolves as a rule of SPECIFICATION.md, and update this count."
          Reference_parser.conflicts_resolved_by_precedence known_conflicts)

let markdown_files = Harness.list_markdown_documents ()

let parse_snippet text =
  let source = Parse_support.make_source text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let items, parser_diagnostics = Reference_parser.Snippet.parse tokens in
  ( tokens,
    items,
    List.map (Syntax_catalog.Lexing_description.render ~text) lexer_diagnostics
    @ List.map (Syntax_catalog.Parsing_description.render ~text) parser_diagnostics )

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          Harness.test
            (Printf.sprintf "%s block %d parses cleanly" name (index + 1))
            (fun () ->
              let _, _, diagnostics = parse_snippet text in
              Parse_support.expect_no_diagnostics text diagnostics))
        (Documents.list_truss_blocks (Parse_support.read_document name)))
    markdown_files

let () =
  Harness.test "a signature without a body in an example is checked" (fun () ->
      let _, _, diagnostics = parse_snippet "fn f(x: Int64)\n  requires x & 1 < 2" in
      if Support.list_codes diagnostics <> [ "parser.needs_parentheses" ] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)))

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          Harness.test
            (Printf.sprintf "%s block %d is accepted by the grammar" name (index + 1))
            (fun () ->
              let tokens, items, _ = parse_snippet text in
              List.iter
                (fun (item : Reference_parser.Snippet.item) ->
                  let slice =
                    Array.to_list (Array.sub tokens item.first (item.stop - item.first))
                  in
                  if
                    not
                      (Reference_parser.accepts
                         (Reference_parser.Snippet.select_entry item.kind)
                         slice)
                  then
                    Harness.fail "the grammar rejects tokens %d to %d of %S" item.first item.stop
                      text)
                items))
        (Documents.list_truss_blocks (Parse_support.read_document name)))
    markdown_files

let () =
  Harness.test "the grammar accepts every Truss file of the repository that the parser accepts"
    (fun () ->
      List.iter
        (fun path ->
          let source =
            Source.create ~path
              (In_channel.with_open_bin (Harness.make_workspace_path path) In_channel.input_all)
          in
          let tokens, lexer_diagnostics = Lexer.lex source in
          let _, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
          if
            lexer_diagnostics = [] && parser_diagnostics = []
            && not (Reference_parser.accepts Reference_parser.parse_file (Array.to_list tokens))
          then Harness.fail "the grammar rejects %s" path)
        (Harness.list_truss_files ()));
  Harness.test "the grammar rejects every input the parser rejects" (fun () ->
      List.iter
        (fun text ->
          let tokens, _ = Lexer.lex (Parse_support.make_source text) in
          if Reference_parser.accepts Reference_parser.parse_file (Array.to_list tokens) then
            Harness.fail "accepted %S" text)
        [
          "fn f() { a & b == c }\n";
          "fn f() { a && b || c }\n";
          "fn f() { x = 0.. }\n";
          "type T = | \n";
        ])

(* The documents agree with the parser: every example parses, GRAMMAR.md's
   grammar accepts exactly the inputs the parser accepts, and
   GRAMMAR.md lists the words the parser recognizes by spelling. *)

open Harness
open Parse_support

(* The documents agree with the code *)

let () =
  test "GRAMMAR.md lists the words the parser recognizes by spelling" (fun () ->
      let listed =
        Documents.words
          (Documents.block_after (document "GRAMMAR.md")
             "name resolution gives the rest their meaning")
      in
      let missing = List.filter (fun word -> not (List.mem word listed)) Parser.spelled_words in
      if missing <> [] then fail "not listed: %s" (String.concat ", " missing))

(* The documents *)

let markdown_files = Harness.markdown_documents ()

let snippet text =
  let source = source text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let items, parser_diagnostics = Reference.Snippet.parse source tokens in
  (tokens, items, lexer_diagnostics @ parser_diagnostics)

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          test
            (Printf.sprintf "%s block %d parses cleanly" name (index + 1))
            (fun () ->
              let _, _, diagnostics = snippet text in
              no_diagnostics text diagnostics))
        (Documents.truss_blocks (document name)))
    markdown_files

let () =
  test "a signature without a body in an example is checked" (fun () ->
      let _, _, diagnostics = snippet "fn f(x: Int64)\n  requires x & 1 < 2" in
      if codes diagnostics <> [ "parser.needs_parentheses" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)))

(* The reference parser *)

let () =
  List.iter
    (fun name ->
      List.iteri
        (fun index text ->
          test
            (Printf.sprintf "%s block %d is accepted by GRAMMAR.md's grammar" name (index + 1))
            (fun () ->
              let tokens, items, _ = snippet text in
              List.iter
                (fun (item : Reference.Snippet.item) ->
                  let slice =
                    Array.to_list (Array.sub tokens item.first (item.stop - item.first))
                  in
                  if not (Reference.accepts (Reference.Snippet.entry item.kind) slice) then
                    fail "the grammar rejects tokens %d to %d of %S" item.first item.stop text)
                items))
        (Documents.truss_blocks (document name)))
    markdown_files

let () =
  test "GRAMMAR.md's grammar accepts a file" (fun () ->
      let text = Fixtures.Parser_documents.grammar_mds_grammar_accepts_a_file in
      let tokens, _ = Lexer.lex (source text) in
      if not (Reference.accepts Reference.file (Array.to_list tokens)) then fail "rejected");
  test "GRAMMAR.md's grammar rejects every input the parser rejects" (fun () ->
      List.iter
        (fun text ->
          let tokens, _ = Lexer.lex (source text) in
          if Reference.accepts Reference.file (Array.to_list tokens) then fail "accepted %S" text)
        [
          "fn f() { a & b == c }\n";
          "fn f() { a && b || c }\n";
          "fn f() { x = 0.. }\n";
          "type T = | \n";
        ])

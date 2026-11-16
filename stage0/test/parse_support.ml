let document name = File_system.read (Harness.workspace_path name)
let source text = Source.create ~path:"test.truss" text

let parse text =
  let tokens, lexer_diagnostics = Lexer.lex (source text) in
  let file, parser_diagnostics = Parser.parse tokens ~lexer_diagnostics in
  let diagnostics = lexer_diagnostics @ parser_diagnostics in
  if
    diagnostics = []
    && List.exists
         (fun (top_level : Syntax.top_level) ->
           List.exists
             (fun (item : Syntax.definition Syntax.item) -> item.positions.recovered <> [])
             (top_level.definition :: top_level.methods))
         file.definitions
  then Harness.fail "the parser recovered in %S with no error" text;
  (file, diagnostics)

let items (file : Syntax.file) =
  List.concat_map
    (fun (top_level : Syntax.top_level) -> top_level.definition :: top_level.methods)
    file.definitions

let codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let no_diagnostics text diagnostics =
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      Harness.fail "unexpected %s at %d: %s in %S"
        (Diagnostic.Code.name diagnostic.code)
        diagnostic.span.start diagnostic.message text)
    diagnostics

let definitions text expected =
  let file, diagnostics = parse text in
  no_diagnostics text diagnostics;
  let actual = Syntax_print.definitions file.definitions in
  Harness.expect_strings ~expected actual

let definition text expected = definitions text [ expected ]

let body_of text =
  let file, diagnostics = parse ("fn example() {\n" ^ text ^ "\n}") in
  match file.definitions with
  | [ { definition = { value = { kind = Function { body; _ }; _ }; _ }; _ } ] ->
      (body.statements, diagnostics)
  | _ -> ([], diagnostics)

let statements text expected =
  let statements, diagnostics = body_of text in
  no_diagnostics text diagnostics;
  let actual = List.map Syntax_print.statement statements in
  Harness.expect_strings ~expected actual

let statement text expected = statements text [ expected ]

let error ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
  match snd (parse text) with
  | [ diagnostic ] -> (
      let message = diagnostic.message in
      if
        message = ""
        || (not (Char.uppercase_ascii message.[0] = message.[0] && message.[0] <> ' '))
        || message.[String.length message - 1] <> '.'
      then Harness.fail "the message %S is not written in sentences" message;
      if diagnostic.code <> Parser code then
        Harness.fail "expected %s, got %s"
          (Diagnostic.Code.name (Parser code))
          (Diagnostic.Code.name diagnostic.code);
      let expected = Support.find_occurrence ~sub:at ~occurrence text in
      if diagnostic.span.start <> expected then
        Harness.fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results = List.map (Diagnostic.apply_fix text) diagnostic.fixes in
      match (fixed, results) with
      | None, [] -> ()
      | None, result :: _ -> Harness.fail "expected no fix, got one giving %S" result
      | Some _, [] -> Harness.fail "expected a fix, got none"
      | Some fixed, results ->
          if fixed :: alternatives <> results then
            Harness.fail "expected the fixes to give [%s], got [%s]"
              (String.concat "; " (List.map (Printf.sprintf "%S") (fixed :: alternatives)))
              (String.concat "; " (List.map (Printf.sprintf "%S") results));
          List.iter
            (fun result ->
              List.iter
                (Harness.fail "the fixed text %S has %s" result)
                (codes (snd (parse result))))
            results)
  | diagnostics ->
      Harness.fail "expected one diagnostic, got [%s] for %S"
        (String.concat "; " (codes diagnostics))
        text

let body_error ?fixed ?alternatives ?occurrence text ~code ~at =
  let wrap text = "fn example() {\n" ^ text ^ "\n}" in
  error ?fixed:(Option.map wrap fixed)
    ?alternatives:(Option.map (List.map wrap) alternatives)
    ?occurrence (wrap text) ~code ~at

let expect_codes expected diagnostics =
  Option.iter (fun expected -> Harness.expect_strings ~expected (codes diagnostics)) expected

let recovered_definitions ?codes:expected_codes text expected =
  let file, diagnostics = parse text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (Syntax_print.definitions file.definitions)

let recovered_statements ?codes:expected_codes text expected =
  let statements, diagnostics = body_of text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (List.map Syntax_print.statement statements)

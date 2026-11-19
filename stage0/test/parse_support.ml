let read_document name = File_system.read (Harness.make_workspace_path name)
let make_source text = Source.create ~path:"test.truss" text

let parse text =
  let file, diagnostics = Parser.parse_source (make_source text) in
  if
    diagnostics = []
    && List.exists
         (fun (top_level : Syntax.top_level) ->
           List.exists
             (fun (item : Syntax.definition Syntax.item) -> item.positions.syntax_errors <> [])
             (top_level.definition :: top_level.methods))
         file.definitions
  then Harness.fail "a syntax error in %S has no diagnostic" text;
  (file, diagnostics)

let list_items (file : Syntax.file) =
  List.concat_map
    (fun (top_level : Syntax.top_level) -> top_level.definition :: top_level.methods)
    file.definitions

let list_codes diagnostics =
  List.map (fun (diagnostic : Diagnostic.t) -> Diagnostic.Code.name diagnostic.code) diagnostics

let expect_no_diagnostics text diagnostics =
  List.iter
    (fun (diagnostic : Diagnostic.t) ->
      Harness.fail "unexpected %s at %d: %s in %S"
        (Diagnostic.Code.name diagnostic.code)
        diagnostic.span.start diagnostic.message text)
    diagnostics

let expect_definitions text expected =
  let file, diagnostics = parse text in
  expect_no_diagnostics text diagnostics;
  let actual = Syntax_print.show_definitions file.definitions in
  Harness.expect_strings ~expected actual

let expect_definition text expected = expect_definitions text [ expected ]

let parse_body text =
  let file, diagnostics = parse ("fn example() {\n" ^ text ^ "\n}") in
  match file.definitions with
  | [ { definition = { value = { kind = Function { body; _ }; _ }; _ }; _ } ] ->
      (body.statements, diagnostics)
  | _ -> ([], diagnostics)

let expect_statements text expected =
  let statements, diagnostics = parse_body text in
  expect_no_diagnostics text diagnostics;
  let actual = List.map Syntax_print.show_statement statements in
  Harness.expect_strings ~expected actual

let expect_statement text expected = expect_statements text [ expected ]

let expect_error ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
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
      let expected = Support.locate_occurrence ~sub:at ~occurrence text in
      if diagnostic.span.start <> expected then
        Harness.fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results =
        List.map
          (fun (fix : Source.span Diagnostic.fix) -> Diagnostic.apply_edits text fix.edits)
          diagnostic.fixes
      in
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
                (list_codes (snd (parse result))))
            results)
  | diagnostics ->
      Harness.fail "expected one diagnostic, got [%s] for %S"
        (String.concat "; " (list_codes diagnostics))
        text

let expect_body_error ?fixed ?alternatives ?occurrence text ~code ~at =
  let wrap text = "fn example() {\n" ^ text ^ "\n}" in
  expect_error ?fixed:(Option.map wrap fixed)
    ?alternatives:(Option.map (List.map wrap) alternatives)
    ?occurrence (wrap text) ~code ~at

let expect_codes expected diagnostics =
  Option.iter (fun expected -> Harness.expect_strings ~expected (list_codes diagnostics)) expected

let expect_recovered_definitions ?codes:expected_codes text expected =
  let file, diagnostics = parse text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (Syntax_print.show_definitions file.definitions)

let expect_recovered_statements ?codes:expected_codes text expected =
  let statements, diagnostics = parse_body text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (List.map Syntax_print.show_statement statements)

let read_document name = File_system.read (Harness.make_workspace_path name)
let make_source text = Source.create ~path:"test.truss" text

let parse text =
  let file, diagnostics = Parser.parse_source (make_source text) in
  let diagnostics = List.map (Syntax_catalog.Syntax_diagnostic.render ~text) diagnostics in
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

let expect_error ?fixed ?alternatives ?occurrence text ~code ~at =
  Support.expect_error
    ~list_diagnostics:(fun text -> snd (parse text))
    ?fixed ?alternatives ?occurrence text ~code:(Parser code) ~at

let expect_body_error ?fixed ?alternatives ?occurrence text ~code ~at =
  let wrap text = "fn example() {\n" ^ text ^ "\n}" in
  expect_error ?fixed:(Option.map wrap fixed)
    ?alternatives:(Option.map (List.map wrap) alternatives)
    ?occurrence (wrap text) ~code ~at

let expect_codes expected diagnostics =
  Option.iter
    (fun expected -> Harness.expect_strings ~expected (Support.list_codes diagnostics))
    expected

let expect_recovered_definitions ?codes:expected_codes text expected =
  let file, diagnostics = parse text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (Syntax_print.show_definitions file.definitions)

let expect_recovered_statements ?codes:expected_codes text expected =
  let statements, diagnostics = parse_body text in
  expect_codes expected_codes diagnostics;
  Harness.expect_strings ~expected (List.map Syntax_print.show_statement statements)

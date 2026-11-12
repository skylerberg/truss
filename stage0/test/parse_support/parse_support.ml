open Harness

let document name = Documents.read (Filename.concat "../.." name)
let source text = Source.create ~path:"test.truss" text

let parse text =
  let source = source text in
  let tokens, lexer_diagnostics = Lexer.lex source in
  let file, parser_diagnostics = Parser.parse source tokens in
  (file, lexer_diagnostics @ parser_diagnostics)

let codes diagnostics = List.map (fun (d : Diagnostic.t) -> Diagnostic.Code.name d.code) diagnostics

let no_diagnostics text diagnostics =
  List.iter
    (fun (d : Diagnostic.t) ->
      fail "unexpected %s at %d: %s in %S" (Diagnostic.Code.name d.code) d.span.start d.message text)
    diagnostics

let definitions text expected =
  let file, diagnostics = parse text in
  no_diagnostics text diagnostics;
  let actual = Syntax_print.definitions file.definitions in
  if actual <> expected then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)

let definition text expected = definitions text [ expected ]

let body_of text =
  let file, diagnostics = parse ("fn example() {\n" ^ text ^ "\n}") in
  match file.definitions with
  | [ { value = { kind = Function { body; _ }; _ }; _ } ] -> (body.statements, diagnostics)
  | _ -> ([], diagnostics)

let statements text expected =
  let statements, diagnostics = body_of text in
  no_diagnostics text diagnostics;
  let actual = List.map Syntax_print.statement statements in
  if actual <> expected then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)

let statement text expected = statements text [ expected ]

let error ?fixed ?(alternatives = []) ?(occurrence = 1) text ~code ~at =
  match snd (parse text) with
  | [ diagnostic ] -> (
      (* Every message is written in sentences, as Diagnostic.t says. *)
      let message = diagnostic.message in
      if
        message = ""
        || (not (Char.uppercase_ascii message.[0] = message.[0] && message.[0] <> ' '))
        || message.[String.length message - 1] <> '.'
      then fail "the message %S is not written in sentences" message;
      if diagnostic.code <> Parser code then
        fail "expected %s, got %s"
          (Diagnostic.Code.name (Parser code))
          (Diagnostic.Code.name diagnostic.code);
      let expected = Documents.find text at ~occurrence in
      if diagnostic.span.start <> expected then
        fail "expected the error at %d (%S), got %d" expected at diagnostic.span.start;
      let results = List.map (Diagnostic.apply_fix text) diagnostic.fixes in
      match (fixed, results) with
      | None, [] -> ()
      | None, result :: _ -> fail "expected no fix, got one giving %S" result
      | Some _, [] -> fail "expected a fix, got none"
      | Some fixed, results ->
          if fixed :: alternatives <> results then
            fail "expected the fixes to give [%s], got [%s]"
              (String.concat "; " (List.map (Printf.sprintf "%S") (fixed :: alternatives)))
              (String.concat "; " (List.map (Printf.sprintf "%S") results));
          List.iter
            (fun result ->
              List.iter (fail "the fixed text %S has %s" result) (codes (snd (parse result))))
            results)
  | diagnostics ->
      fail "expected one diagnostic, got [%s] for %S" (String.concat "; " (codes diagnostics)) text

let body_error ?fixed ?alternatives ?occurrence text ~code ~at =
  let wrap text = "fn example() {\n" ^ text ^ "\n}" in
  error ?fixed:(Option.map wrap fixed)
    ?alternatives:(Option.map (List.map wrap) alternatives)
    ?occurrence (wrap text) ~code ~at

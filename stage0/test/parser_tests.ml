let () =
  Harness.test "definitions are split at line breaks outside brackets" (fun () ->
      Parse_support.expect_definitions "fn first() {}\nfn second() {}"
        [ "(fn first () (block))"; "(fn second () (block))" ]);
  Harness.test "a body on the next line stays with its signature" (fun () ->
      Parse_support.expect_definition "fn first()\n  uses Clock\n{\n  todo\n}"
        "(fn first () (uses Clock) (block todo))");
  Harness.test "use lines are kept apart from definitions" (fun () ->
      let file, diagnostics =
        Parse_support.parse "use standard::json\nuse weather::forecast::hourly\nfn f() {}"
      in
      Parse_support.expect_no_diagnostics "" diagnostics;
      if
        List.map
          (fun (item : Syntax.path Syntax.item) -> Syntax_print.show_path item.value)
          file.uses
        <> [ "standard::json"; "weather::forecast::hourly" ]
      then Harness.fail "wrong use lines");
  Harness.test "a use line after a definition moves up" (fun () ->
      Parse_support.expect_error "use a::b\n\nfn f() {}\nuse c::d\n" ~code:Use_after_definition
        ~at:"use c::d" ~fixed:"use a::b\nuse c::d\n\nfn f() {}\n");
  Harness.test "a use line after the first definition moves above it" (fun () ->
      Parse_support.expect_error "fn f() {}\nuse c::d\n" ~code:Use_after_definition ~at:"use c::d"
        ~fixed:"use c::d\nfn f() {}\n");
  Harness.test "a statement at the top level is one error" (fun () ->
      Parse_support.expect_error "fn f() {}\nx = 1\nfn g() {}" ~code:Statement_at_top_level ~at:"x");
  Harness.test "a definition records where the parser recovered" (fun () ->
      let list_recovered text =
        match Parse_support.list_items (fst (Parse_support.parse text)) with
        | [ item ] ->
            List.map
              (fun (span : Source.Definition_span.t) ->
                String.sub text (item.base + span.start) (span.stop - span.start))
              item.positions.recovered
        | _ -> [ "wrong definitions" ]
      in
      if list_recovered "fn f() {\n  x as Int64\n}" <> [ "as" ] then
        Harness.fail "the habit is not recorded";
      if list_recovered "fn f() {\n  let x = (1 +\n}" = [] then
        Harness.fail "the inserted closer is not recorded";
      if list_recovered "fn f() {\n  let x = 0755\n}" <> [ "0755" ] then
        Harness.fail "the lexer's error is not recorded";
      if list_recovered "fn f() {\n  assert true\n}" = [] then
        Harness.fail "a rule checked after parsing is not recorded";
      if list_recovered "fn f(x: Int64) -> Int64" = [] then
        Harness.fail "the missing body is not recorded");
  Harness.test "a lexer error in a method is recorded in the method alone" (fun () ->
      let text = "impl Clock for Fixed {\n  fn now(self) -> Instant {\n    0755\n  }\n}" in
      match Parse_support.list_items (fst (Parse_support.parse text)) with
      | [ container; method_ ] ->
          if container.positions.recovered <> [] then Harness.fail "recorded in the container";
          if method_.positions.recovered = [] then Harness.fail "not recorded in the method"
      | items -> Harness.fail "expected a container and a method, got %d items" (List.length items));
  Harness.test "a parser error in a definition with a lexer error has no fix" (fun () ->
      let _, diagnostics = Parse_support.parse "fn f() {\n  let x = 0755\n  count++\n}" in
      match
        List.find_opt
          (fun (diagnostic : Diagnostic.t) -> diagnostic.code = Parser Increment)
          diagnostics
      with
      | Some { fixes = []; _ } -> ()
      | Some _ -> Harness.fail "offered a fix"
      | None -> Harness.fail "no parser.increment");
  Harness.test "a missing body after another error in the definition has no fix" (fun () ->
      let _, diagnostics =
        Parse_support.parse
          "fn f(key: UInt64) -> Bool\n  cost allocations == match\n  {\n    key < 1\n  }\n"
      in
      match
        List.find_opt
          (fun (diagnostic : Diagnostic.t) -> diagnostic.code = Parser Missing_body)
          diagnostics
      with
      | Some { fixes = []; _ } -> ()
      | Some _ -> Harness.fail "offered a fix"
      | None -> Harness.fail "no parser.missing_body");
  Harness.test "a missing body's recovery is where the body starts" (fun () ->
      let tokens, _ = Lexer.lex (Parse_support.make_source "fn f(x: Int64) -> Int64\nfn g() {}") in
      match
        Parser.For_testing.parse_definition tokens (List.hd (Parser.For_testing.split tokens))
      with
      | ( {
            definition =
              { value = { kind = Function { body; _ }; _ }; positions = { spans; recovered }; _ };
            _;
          },
          _ ) ->
          let body_start = spans.(body.id).start in
          if
            List.map (fun (span : Source.Definition_span.t) -> (span.start, span.stop)) recovered
            <> [ (body_start, body_start) ]
          then Harness.fail "recovered at the wrong place"
      | _ -> Harness.fail "the signature was not kept");
  Harness.test "a recovery at the end of a body lies in the body" (fun () ->
      match
        Parse_support.list_items (fst (Parse_support.parse "fn f() {\n  let x = (1 +\nfn g() {}\n"))
      with
      | { value = { kind = Function { body; _ }; _ }; positions = { spans; recovered }; _ } :: _ ->
          let body_span = spans.(body.id) in
          if
            not
              (List.exists
                 (fun (span : Source.Definition_span.t) ->
                   span.start < span.stop && body_span.start <= span.start
                   && span.start < body_span.stop)
                 recovered)
          then Harness.fail "no recovery inside the body"
      | _ -> Harness.fail "wrong definitions");
  Harness.test "a failed clause at the end lies in the signature" (fun () ->
      match Parse_support.list_items (fst (Parse_support.parse "fn f() requires")) with
      | { value = { kind = Function { body; _ }; _ }; positions = { spans; recovered }; _ } :: _ ->
          if
            not
              (List.exists
                 (fun (span : Source.Definition_span.t) -> span.start < spans.(body.id).start)
                 recovered)
          then Harness.fail "no recovery in the signature"
      | _ -> Harness.fail "wrong definitions");
  Harness.test "a definition whose header did not parse keeps its keyword and name" (fun () ->
      Parse_support.expect_recovered_definitions
        "fn List[Element].sort[](mut self) {}\ntype Point = 1\nfn f() {}"
        [ "(error fn List[Element].sort)"; "(error type Point)"; "(fn f () (block))" ]);
  Harness.test "a failed const keeps its name" (fun () ->
      let tokens, _ = Lexer.lex (Parse_support.make_source "const pi: Float64 = 1 +") in
      let top_level, _ =
        Parser.For_testing.parse_definition tokens (List.hd (Parser.For_testing.split tokens))
      in
      let printed = Syntax_print.show_definition top_level.definition.value in
      if printed <> "(error let pi)" then Harness.fail "got %s" printed);
  Harness.test "a failed definition keeps its visibility" (fun () ->
      Parse_support.expect_recovered_definitions "public fn f() -> {\n}\nfn g() {}"
        [ "(public (error fn f))"; "(fn g () (block))" ]);
  Harness.test "a function without a body keeps its signature" (fun () ->
      Parse_support.expect_recovered_definitions "fn f(x: Int64) -> Int64\nfn g() {}"
        [ "(fn f ((x: Int64)) -> Int64 (block error))"; "(fn g () (block))" ]);
  Harness.test "the definition after a broken one parses" (fun () ->
      let file, diagnostics = Parse_support.parse "fn f() -> {\n}\nfn g() {}" in
      if List.length diagnostics <> 1 then
        Harness.fail "expected one diagnostic, got [%s]"
          (String.concat "; " (Parse_support.list_codes diagnostics));
      match Parse_support.list_items file with
      | [ _; { value = { kind = Function _; _ }; _ } ] -> ()
      | _ -> Harness.fail "g did not parse");
  Harness.test "a missing } does not swallow the next definition" (fun () ->
      let file, diagnostics = Parse_support.parse "fn f() {\n  todo\nfn g() {}" in
      if Parse_support.list_codes diagnostics <> [ "lexer.unclosed_bracket" ] then
        Harness.fail "got [%s]" (String.concat "; " (Parse_support.list_codes diagnostics));
      if List.length file.definitions <> 2 then Harness.fail "expected two definitions")

let () =
  Harness.test "spans are relative to the definition" (fun () ->
      match Parse_support.list_items (fst (Parse_support.parse "fn f() {}\n\nfn g() {}")) with
      | [ _; second ] ->
          if second.base <> 11 then Harness.fail "base %d" second.base;
          let span = second.positions.spans.(second.value.id) in
          if span.start <> 0 || span.stop <> 9 then Harness.fail "span";
          if second.stop <> 20 then Harness.fail "stop %d" second.stop
      | _ -> Harness.fail "expected two definitions");
  Harness.test "moving a definition changes nothing in its tree" (fun () ->
      let text =
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  let total = \"${items.length()}\"\n\
        \  items[0] + 1\n\
         }"
      in
      match
        ( Parse_support.list_items (fst (Parse_support.parse text)),
          Parse_support.list_items (fst (Parse_support.parse ("fn g() {}\n\n\n" ^ text))) )
      with
      | [ alone ], [ _; moved ] ->
          if alone.value <> moved.value then Harness.fail "the trees differ";
          if alone.positions <> moved.positions then Harness.fail "the positions differ"
      | _ -> Harness.fail "wrong definitions");
  Harness.test "interpolations are parsed with the definition's base" (fun () ->
      match
        Parse_support.list_items (fst (Parse_support.parse "fn g() {}\nfn f() { \"${x + 1}\" }"))
      with
      | [
       _;
       {
         value =
           {
             kind =
               Function
                 {
                   body =
                     {
                       statements =
                         [
                           {
                             kind = Expression { kind = String { rest = [ (value, _) ]; _ }; _ };
                             _;
                           };
                         ];
                       _;
                     };
                   _;
                 };
             _;
           };
         positions = { spans; _ };
         _;
       };
      ] ->
          let start = spans.(value.id).start in
          if start <> 12 then Harness.fail "interpolation span %d" start
      | _ -> Harness.fail "wrong tree");
  Harness.test "nesting deeper than the limit is one error, not a stack overflow" (fun () ->
      let text = "fn f() { " ^ String.make 300 '(' ^ "1" ^ String.make 300 ')' ^ " }" in
      if Parse_support.list_codes (snd (Parse_support.parse text)) <> [ "parser.nesting_too_deep" ]
      then
        Harness.fail "got [%s]"
          (String.concat "; " (Parse_support.list_codes (snd (Parse_support.parse text)))))

let () =
  let list_too_deep text =
    List.filter (( = ) "parser.nesting_too_deep")
      (Parse_support.list_codes (snd (Parse_support.parse text)))
  in
  Harness.test "nested echo counts toward the limit" (fun () ->
      let text =
        "fn f() {\n  let x = " ^ String.concat "" (List.init 300 (fun _ -> "echo ")) ^ "1\n}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested if counts toward the limit" (fun () ->
      let text =
        "fn f() {\n  let x = "
        ^ String.concat "" (List.init 300 (fun _ -> "if "))
        ^ "x"
        ^ String.concat "" (List.init 300 (fun _ -> " {}"))
        ^ "\n}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested loop bodies count toward the limit" (fun () ->
      let text =
        "fn f() {\n"
        ^ String.concat "" (List.init 300 (fun _ -> "while x {\n"))
        ^ String.concat "" (List.init 300 (fun _ -> "}\n"))
        ^ "}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested blocks without expressions count toward the limit" (fun () ->
      let text =
        "fn f() {\n"
        ^ String.concat "" (List.init 300 (fun _ -> "parallel {\n"))
        ^ String.concat "" (List.init 300 (fun _ -> "}\n"))
        ^ "}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested types count toward the limit" (fun () ->
      let text =
        "fn f(value: "
        ^ String.concat "" (List.init 300 (fun _ -> "List["))
        ^ "Int64" ^ String.make 300 ']' ^ ") {}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested patterns count toward the limit" (fun () ->
      let text =
        "fn f() {\n  match x {\n    "
        ^ String.concat "" (List.init 300 (fun _ -> "Some("))
        ^ "y" ^ String.make 300 ')' ^ " => todo\n  }\n}"
      in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "nested prefix operators count toward the limit" (fun () ->
      let text = "fn f() {\n  let x = " ^ String.make 300 '!' ^ "y\n}" in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  let make_chain ~first ~link ~last =
    first ^ String.concat "" (List.init 10_001 (fun _ -> link)) ^ last
  in
  Harness.test "a chain of binary operators longer than the limit is one error" (fun () ->
      let text = make_chain ~first:"fn f() {\n  let x = 1" ~link:" + 1" ~last:"\n}" in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "a chain of postfix operations longer than the limit is one error" (fun () ->
      let text = make_chain ~first:"fn f() {\n  let x = a" ~link:".b" ~last:"\n}" in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "a chain of else if branches longer than the limit is one error" (fun () ->
      let text = make_chain ~first:"fn f() {\n  if a {}" ~link:" else if a {}" ~last:"\n}" in
      if list_too_deep text <> [ "parser.nesting_too_deep" ] then Harness.fail "no nesting error");
  Harness.test "a chain longer than the nesting limit is not nested" (fun () ->
      let text =
        "fn f() {\n  let x = 1" ^ String.concat "" (List.init 300 (fun _ -> " + a.b")) ^ "\n}"
      in
      if Parse_support.list_codes (snd (Parse_support.parse text)) <> [] then
        Harness.fail "a diagnostic");
  Harness.test "an inserted closer in an inner statement leaves errors in the outer one reported"
    (fun () ->
      let _, diagnostics = Parse_support.parse "fn f() {\n  let x = run(fn() { g( }) +\n}" in
      if
        Parse_support.list_codes diagnostics
        <> [ "lexer.unclosed_bracket"; "parser.unexpected_token" ]
      then Harness.fail "got [%s]" (String.concat "; " (Parse_support.list_codes diagnostics)))

let () =
  let split_pieces text =
    let source = Parse_support.make_source text in
    let tokens, _ = Lexer.lex source in
    (source, tokens, Parser.For_testing.split tokens)
  in
  Harness.test "a method is a definition of its own, inside its impl" (fun () ->
      let text = "impl Clock for Fixed {\n  fn now(self) -> Instant {\n    todo\n  }\n}" in
      let file, _ = Parse_support.parse text in
      match file.definitions with
      | [ { methods = [ method_ ]; _ } ] ->
          let method_text = String.sub text method_.base (method_.stop - method_.base) in
          if method_text <> "fn now(self) -> Instant {\n    todo\n  }" then
            Harness.fail "the method's text is %S" method_text;
          if method_.base <> 25 then Harness.fail "the method starts at %d" method_.base
      | _ -> Harness.fail "expected an impl holding one method");
  Harness.test "a method's tree does not depend on its surroundings" (fun () ->
      let parse_method text =
        match Parse_support.list_items (fst (Parse_support.parse text)) with
        | [ _; method_ ] -> method_.value
        | _ -> failwith "expected an impl and its method"
      in
      let method_text = "  fn now(self) -> Instant {\n    todo\n  }\n" in
      if
        parse_method ("impl Clock for Fixed {\n" ^ method_text ^ "}")
        <> parse_method
             ("impl Clock for Other[Element] uses Random {\n  type Tick = Int64\n\n" ^ method_text
            ^ "}")
      then Harness.fail "the trees differ");
  Harness.test "a definition's diagnostics are placed in the file by its base" (fun () ->
      match split_pieces "fn g() {}\nfn f() { x = }" with
      | _, tokens, [ _; second ] -> (
          match snd (Parser.For_testing.parse_definition tokens second) with
          | [ diagnostic ] ->
              if diagnostic.span.start <> 23 then Harness.fail "start %d" diagnostic.span.start
          | _ -> Harness.fail "expected one diagnostic")
      | _ -> Harness.fail "expected two pieces");
  Harness.test "moving a broken definition changes nothing in its tree" (fun () ->
      let text = "fn f(items: List[Int64]) {\n  let total = items[0] +\n}" in
      let parse_tree text =
        let _, tokens, pieces = split_pieces text in
        let last = List.nth pieces (List.length pieces - 1) in
        (fst (Parser.For_testing.parse_definition tokens last)).definition.value
      in
      if parse_tree text <> parse_tree ("fn g() {}\n\n\n" ^ text) then
        Harness.fail "the trees differ");
  Harness.test "indenting a method changes neither its tree nor its diagnostics" (fun () ->
      let parse_indented_method ~indentation =
        let source, tokens, pieces =
          split_pieces ("impl Clock for Fixed {\n" ^ indentation ^ "fn now(self) -> Instant\n}")
        in
        match Parser.For_testing.parse_definition tokens (List.hd pieces) with
        | { methods = [ method_ ]; _ }, diagnostics ->
            if diagnostics = [] then Harness.fail "the method has no diagnostic";
            ( method_.value,
              String.sub (Source.text source) method_.base (method_.stop - method_.base),
              List.map
                (fun (diagnostic : Diagnostic.t) ->
                  (diagnostic.code, diagnostic.span.start - method_.base))
                diagnostics )
        | _ -> failwith "expected one method"
      in
      if parse_indented_method ~indentation:"  " <> parse_indented_method ~indentation:"\t\t" then
        Harness.fail "the results differ");
  Harness.test "an example's diagnostics include those of the methods declared inside it" (fun () ->
      let _, tokens, pieces =
        split_pieces "impl Clock for Fixed {\n  fn now(self) -> { todo }\n}"
      in
      match Parser.For_testing.parse_example_definition tokens (List.hd pieces) with
      | _, [ diagnostic ] ->
          if Diagnostic.Code.name diagnostic.code <> "parser.unexpected_token" then
            Harness.fail "code %s" (Diagnostic.Code.name diagnostic.code);
          if diagnostic.span.start <> 41 then Harness.fail "start %d" diagnostic.span.start
      | _, diagnostics -> Harness.fail "%d diagnostics" (List.length diagnostics))

let () =
  Harness.test "Layout lets every token in the first set of a statement begin one" (fun () ->
      let kinds =
        List.map (fun (_, keyword) -> Token.Keyword keyword) Token.keywords
        @ List.map (fun (_, punctuation) -> Token.Punctuation punctuation) Token.punctuation
        @ [
            Upper "Name";
            Lower "name";
            Underscore;
            Integer Z.one;
            Float (Token.Decimal.normalize ~significand:Z.one ~exponent:Z.zero);
            String
              {
                tag = None;
                form = Ordinary;
                first = { value = ""; span = Source.make_zero_width 0 };
                rest = [||];
              };
          ]
      in
      let only_in_brackets = [ Token.Punctuation Dot_dot; Punctuation Dot_dot_equal ] in
      List.iter
        (fun kind ->
          if
            Parser.For_testing.begins_statement kind
            && (not (Token.can_begin kind))
            && not (List.mem kind only_in_brackets)
          then
            Harness.fail "%s begins a statement, but a line break before it is not a NEWLINE"
              (match kind with
              | Keyword keyword -> Token.spell_keyword keyword
              | Punctuation punctuation -> Token.spell_punctuation punctuation
              | _ -> "a name or a literal"))
        kinds)

let list_ids (definition : Syntax.definition) =
  let ids = ref [] in
  let rec check_expression ~parent (value : Syntax.expression) =
    if value.id >= parent then
      Harness.fail "an expression's id %d is not before its parent's %d" value.id parent;
    ids := value.id :: !ids;
    Syntax_walk.visit_expression_parts
      ~on_expression:(check_expression ~parent:value.id)
      ~on_statement:(check_statement ~parent:value.id)
      value
  and check_statement ~parent (written : Syntax.statement) =
    if written.id >= parent then
      Harness.fail "a statement's id %d is not before its parent's %d" written.id parent;
    ids := written.id :: !ids;
    Syntax_walk.visit_statement_parts
      ~on_expression:(check_expression ~parent:written.id)
      ~on_statement:(check_statement ~parent:written.id)
      written
  in
  Syntax_walk.visit_definition (check_expression ~parent:definition.id) definition;
  !ids

let () =
  Harness.test "ids are unique within a definition, children first" (fun () ->
      match
        Parse_support.list_items
          (fst
             (Parse_support.parse
                "fn f(items: List[Int64]) -> Int64 {\n\
                \  let x = items[0] + \"${items.length()}\"\n\
                \  if x > 0 { x } else { 0 }\n\
                 }"))
      with
      | [ { value; _ } ] ->
          let ids = list_ids value in
          if List.length (List.sort_uniq compare ids) <> List.length ids then
            Harness.fail "ids repeat";
          if ids = [] then Harness.fail "no ids"
      | _ -> Harness.fail "wrong definitions");
  Harness.test "a definition whose header was read again has an id of its own" (fun () ->
      match
        Parse_support.list_items (fst (Parse_support.parse "fn List[Element].sort[](mut self) {}"))
      with
      | [
       {
         value = { kind = Definition_error { name = Some (Member_name (head, name)); _ }; id; _ };
         _;
       };
      ] ->
          if List.length (List.sort_uniq compare [ id; head.id; name.id ]) <> 3 then
            Harness.fail "ids repeat"
      | _ -> Harness.fail "wrong definitions")

let () =
  let expect_type text expected =
    Parse_support.expect_definition
      ("fn f(value: " ^ text ^ ") {}")
      ("(fn f ((value: " ^ expected ^ ")) (block))")
  in
  Harness.test "a path type with arguments" (fun () ->
      expect_type "standard::json::Map[String, List[Int64]]"
        "standard::json::Map[String, List[Int64]]");
  Harness.test "a count argument and a count parameter" (fun () ->
      expect_type "Array[UInt8, 32]" "Array[UInt8, 32]";
      expect_type "Array[Int64, count]" "Array[Int64, count]");
  Harness.test "Self and its associated types" (fun () ->
      expect_type "Self" "Self";
      expect_type "Self.Key" "Self.Key");
  Harness.test "an associated type of a parameter" (fun () ->
      expect_type "Items.Element" "Items.Element");
  Harness.test "any with a constraint" (fun () ->
      expect_type "any Cursor[Element = Int64]" "(any Cursor[Element = Int64])");
  Harness.test "a function type" (fun () ->
      expect_type "fn(mut Element, Element) -> Ordering" "(fn (mut Element Element) -> Ordering)");
  Harness.test "a function type in parentheses with clauses" (fun () ->
      expect_type "(fn(Item) uses Clock, Random cost time O(1))"
        "(fn (Item) (uses Clock Random) (cost time (O 1)))");
  Harness.test "parentheses around a function type need clauses" (fun () ->
      Parse_support.expect_error "fn f(value: (fn(Item))) {}" ~code:Unexpected_token ~at:"(fn");
  Harness.test "a function type's requires names its inputs" (fun () ->
      Parse_support.expect_definition "fn f(visit: (fn(index: UInt64) requires index < 3)) {}"
        "(fn f ((visit: (fn (index: UInt64) (requires (< index 3))))) (block))");
  Harness.test "requires in a function type needs every input named" (fun () ->
      Parse_support.expect_error "fn f(value: (fn(Item) requires true)) {}"
        ~code:Function_type_names ~at:"fn(Item)");
  Harness.test "a function type without requires names no input" (fun () ->
      Parse_support.expect_error "fn f(value: fn(item: Item)) {}" ~code:Function_type_names
        ~at:"fn(item");
  Harness.test "ensures in a function type" (fun () ->
      Parse_support.expect_error "fn f(value: (fn(item: Item) ensures true)) {}"
        ~code:Unexpected_token ~at:"ensures");
  Harness.test "requires on a function type that is not a parameter's" (fun () ->
      Parse_support.expect_error "type T(visit: (fn(index: UInt64) requires index < 3))"
        ~code:Misplaced_requires ~at:"requires";
      Parse_support.expect_error "fn f(visits: List[(fn(index: UInt64) requires index < 3)]) {}"
        ~code:Misplaced_requires ~at:"requires");
  Harness.test "generic parameters" (fun () ->
      Parse_support.expect_definition "fn f[Key: Hash + Ordered, count: UInt64]() {}"
        "(fn f[Key: Hash + Ordered, count: UInt64] () (block))");
  Harness.test "a capability parameter is written `generic` at each use" (fun () ->
      Parse_support.expect_definition
        "fn f(visit: (fn() uses Clock, generic Granted)) uses generic Granted {}"
        "(fn f ((visit: (fn () (uses Clock generic Granted)))) (uses generic Granted) (block))")

let () =
  let expect_pattern text expected =
    Parse_support.expect_statement ("let " ^ text ^ " = value") ("(let " ^ expected ^ " value)")
  in
  let expect_arm text expected =
    Parse_support.expect_statement
      ("match value {\n  " ^ text ^ " => todo\n}")
      ("(match (value) (=> " ^ expected ^ " todo))")
  in
  Harness.test "a binding" (fun () -> expect_pattern "name" "name");
  Harness.test "a wildcard" (fun () -> expect_pattern "_" "_");
  Harness.test "a record pattern" (fun () ->
      expect_pattern "(index, element: score, ..)" "(record index (element: score) ..)");
  Harness.test "a variant pattern" (fun () ->
      expect_arm "Some(Circle(radius, ..))" "(Some (Circle radius ..))");
  Harness.test "qualified constants" (fun () ->
      expect_arm "http::ok" "http::ok";
      expect_arm "Status.teapot" "Status.teapot";
      expect_arm "http::Status.teapot" "http::Status.teapot");
  Harness.test "literals" (fun () ->
      expect_arm "-1" "-1";
      expect_arm "\"GET\"" "\"GET\"";
      expect_arm "Character\"a\"" "Character\"a\"");
  Harness.test "alternatives" (fun () -> expect_arm "301 | 302 | Low" "(| 301 302 Low)");
  Harness.test "ranges" (fun () ->
      expect_arm "500..=599" "(..= 500 599)";
      expect_arm "0..=network::max_port" "(..= 0 network::max_port)";
      expect_arm "UInt16.minimum..=UInt16.maximum" "(..= UInt16.minimum UInt16.maximum)";
      expect_arm "Character\"a\"..=Character\"z\"" "(..= Character\"a\" Character\"z\")");
  Harness.test "a guard" (fun () -> expect_arm "code if code >= 400" "code (if (>= code 400))");
  Harness.test "several values" (fun () ->
      Parse_support.expect_statement "match state, event {\n  Idle | Paused, Tick => todo\n}"
        "(match (state event) (=> (| Idle Paused) Tick todo))");
  Harness.test ".. must be the last field" (fun () ->
      Parse_support.expect_body_error "let (.., x) = value" ~code:Unexpected_token ~at:"..");
  Harness.test "a float literal is not a pattern" (fun () ->
      Parse_support.expect_body_error "match x {\n  0.0 => todo\n}" ~code:Float_pattern ~at:"0.0");
  Harness.test "a range's end is a literal or a constant written with its module or type" (fun () ->
      Parse_support.expect_body_error "match x {\n  0..=max_port => todo\n}" ~code:Unexpected_token
        ~at:"max_port";
      Parse_support.expect_body_error "match x {\n  low..=9 => todo\n}" ~code:Unexpected_token
        ~at:"low");
  Harness.test "a range pattern needs both ends" (fun () ->
      Parse_support.expect_body_error "match x {\n  0.. => todo\n}" ~code:Unexpected_token ~at:"=>");
  Harness.test "a string in a pattern cannot interpolate" (fun () ->
      Parse_support.expect_body_error "match x {\n  \"${y}\" => todo\n}"
        ~code:Interpolation_not_allowed ~at:"\"${")

let () =
  let expect_expression text expected =
    Parse_support.expect_statement ("let x = " ^ text) ("(let x " ^ expected ^ ")")
  in
  Harness.test "arithmetic precedence" (fun () ->
      expect_expression "a + b * c - d" "(- (+ a (* b c)) d)");
  Harness.test "prefix binds tighter than infix" (fun () ->
      expect_expression "-x.abs() + !ready" "(+ (- (call (. x abs))) (! ready))");
  Harness.test "ranges bind more loosely than arithmetic" (fun () ->
      expect_expression "0..count - 1" "(.. 0 (- count 1))");
  Harness.test "comparison and logic" (fun () ->
      expect_expression "a < b && c is Some(d)" "(&& (< a b) (is c (Some d)))");
  Harness.test "implication binds most loosely" (fun () ->
      Parse_support.expect_definition "fn f() requires a && b ==> c || d {}"
        "(fn f () (requires (==> (&& a b) (|| c d))) (block))");
  Harness.test "postfix operators" (fun () ->
      expect_expression "a.b[0](c, label: d)?.e with (f.g: 1, h)"
        "(with (. (? (call ([] (. a b) 0) c (label: d))) e) (f.g: 1) h)");
  Harness.test "modes and any take a postfix expression" (fun () ->
      Parse_support.expect_statement "mut config.servers.sort()"
        "(mut (call (. (. config servers) sort)))";
      expect_expression "any UserRoutes(users: [:])" "(any (call UserRoutes (users: (map))))");
  Harness.test "own with an update" (fun () ->
      expect_expression "own config with (debug: true)" "(own (with config (debug: true)))");
  Harness.test "open ranges in brackets" (fun () ->
      expect_expression "items[2..]" "([] items (.. 2 _))";
      expect_expression "items[..3]" "([] items (.. _ 3))";
      expect_expression "items[..=3]" "([] items (..= _ 3))");
  Harness.test "an open range outside brackets" (fun () ->
      Parse_support.expect_body_error "for i in 0.. {}" ~code:Open_range ~at:"..");
  Harness.test "an open start outside brackets" (fun () ->
      Parse_support.expect_body_error "let x = ..3" ~code:Open_range ~at:"..");
  Harness.test "an open range is alone in its brackets" (fun () ->
      Parse_support.expect_body_error "let x = items[1.., 4]" ~code:Open_range ~at:"..");
  Harness.test "a range that includes its end has an end" (fun () ->
      Parse_support.expect_body_error "let x = items[1..=]" ~code:Open_range ~at:"..=");
  Harness.test "an open range has no comma after it" (fun () ->
      Parse_support.expect_body_error "let x = items[1..,]" ~code:Open_range ~at:","
        ~fixed:"let x = items[1..]");
  Harness.test "a bare name does not end a range pattern" (fun () ->
      Parse_support.expect_body_error "match x {\n  lo..hi => 1\n  _ => 0\n}" ~code:Unexpected_token
        ~at:"lo");
  Harness.test "a lambda's body may start on the next line" (fun () ->
      Parse_support.expect_statement "let f: fn(Job) -> Bool = fn(job)\n{\n  job.ready\n}"
        "(let f : (fn (Job) -> Bool) (fn (job) (block (. job ready))))");
  Harness.test "as at the end of a line is not read with the next line" (fun () ->
      Parse_support.expect_body_error "let n = size as\nlet m = 1" ~code:Reserved_word ~at:"as");
  Harness.test "brackets cannot be empty" (fun () ->
      Parse_support.expect_body_error "let x = items[]" ~code:Unexpected_token ~at:"]");
  Harness.test "i++ is recognized only at the end of a line" (fun () ->
      Parse_support.expect_body_error "count++ x" ~code:Unexpected_token ~at:"++");
  Harness.test "type arguments and constraints in brackets" (fun () ->
      expect_expression "List[String].with_capacity(64)"
        "(call (. ([] List String) with_capacity) 64)";
      expect_expression "total[Iterable[Element = Int64]]"
        "([] total ([] Iterable Element = Int64))");
  Harness.test "a collection cannot mix list elements and map entries" (fun () ->
      Parse_support.expect_body_error "let x = [1, \"a\": 2]" ~code:Unexpected_token ~at:"\"a\"";
      Parse_support.expect_body_error "let x = [\"a\": 1, 2]" ~code:Unexpected_token ~at:"2]");
  Harness.test "a field and an update that do not parse are errors in the tree" (fun () ->
      Parse_support.expect_recovered_definitions "type T(x: Int64, 1)"
        [ "(type T ((x: Int64) error))" ];
      Parse_support.expect_recovered_statements "let y = x with (1)" [ "(let y (with x error))" ]);
  Harness.test "lists and maps" (fun () ->
      expect_expression "[1, 2,]" "(list 1 2)";
      expect_expression "[]" "(list)";
      expect_expression "[\"http\": 80, name: 1]" "(map (\"http\" 80) (name 1))";
      expect_expression "[:]" "(map)");
  Harness.test "a lambda" (fun () ->
      expect_expression "fn(sum, (value, ..)) { sum + value }"
        "(fn (sum (record value ..)) (block (+ sum value)))");
  Harness.test "if, else if, and else" (fun () ->
      expect_expression "if a { 1 } else if b { 2 } else { 3 }"
        "(if a (block 1) (if b (block 2) (block 3)))");
  Harness.test "provide" (fun () ->
      expect_expression "provide mut files, DiscardLog() { run() }"
        "(provide ((mut files) (call DiscardLog)) (block (call run)))");
  Harness.test "a block" (fun () ->
      expect_expression "{\n  let y = 1\n  y\n}" "(block (let y 1) y)");
  Harness.test "return with and without a value" (fun () ->
      Parse_support.expect_statement "return" "(return)";
      Parse_support.expect_statement "return { 1 }" "(return (block 1))";
      Parse_support.expect_statements "if a { return }\nb" [ "(if a (block (return)))"; "b" ]);
  Harness.test "echo takes everything after it" (fun () ->
      expect_expression "echo player.wins * 3" "(echo (* (. player wins) 3))");
  Harness.test "strings, tagged strings, and interpolations" (fun () ->
      expect_expression "\"a${b + 1}c\"" "\"a${(+ b 1)}c\"";
      expect_expression "database::SqlQuery\"select ${id}\"" "database::SqlQuery\"select ${id}\"";
      expect_expression "\"${names.join(\", \")}\"" "\"${(call (. names join) \", \")}\"");
  Harness.test "no missing token is reported at the end of an interpolation that a line break ended"
    (fun () ->
      let _, diagnostics = Parse_support.parse "fn f() {\n  let x = \"\"\"a ${b ? c\n  \"\"\"\n}" in
      if
        List.filter
          (fun code -> String.starts_with ~prefix:"parser." code)
          (Parse_support.list_codes diagnostics)
        <> []
      then Harness.fail "got [%s]" (String.concat "; " (Parse_support.list_codes diagnostics)));
  Harness.test "an error in an interpolation stays there" (fun () ->
      let statements, diagnostics = Parse_support.parse_body "let x = \"${a +}\"\nlet y = 1" in
      if Parse_support.list_codes diagnostics <> [ "parser.unexpected_token" ] then
        Harness.fail "got [%s]" (String.concat "; " (Parse_support.list_codes diagnostics));
      if List.length statements <> 2 then Harness.fail "expected two statements");
  Harness.test "constants and names" (fun () ->
      expect_expression "true" "true";
      expect_expression "Self.Key" "(. Self Key)";
      expect_expression "geometry::Shape.Circle" "(. geometry::Shape Circle)";
      expect_expression "json::parse" "json::parse");
  Harness.test "quantifiers in a specification" (fun () ->
      Parse_support.expect_definition
        "fn f() requires count > 0 && forall i in 0..count => items[i] > 0 || done {}"
        "(fn f () (requires (&& (> count 0) (forall (in i (.. 0 count)) (|| (> ([] items i) 0) \
         done)))) (block))";
      Parse_support.expect_definition "fn f() requires forall value: Int64 => value + 0 == value {}"
        "(fn f () (requires (forall value: Int64 (== (+ value 0) value))) (block))")

let () =
  Harness.test "let and var with annotations" (fun () ->
      Parse_support.expect_statements "let a: Int64 = 1\nvar (low, high) = bounds"
        [ "(let a : Int64 1)"; "(var (record low high) bounds)" ]);
  Harness.test "let ... else" (fun () ->
      Parse_support.expect_statement "let Some(user) = find(id) else {\n  return\n}"
        "(let (Some user) (call find id) (else (block (return))))");
  Harness.test "the expression before let ... else cannot end with }" (fun () ->
      Parse_support.expect_body_error "let Some(x) = if ready { a } else { b } else { return }"
        ~code:Let_else_brace ~at:"else { return"
        ~fixed:"let Some(x) = (if ready { a } else { b }) else { return }");
  Harness.test "assignments" (fun () ->
      Parse_support.expect_statements "a = 1\nitems[i] += 2\nflags |= mask"
        [ "(= a 1)"; "(+= ([] items i) 2)"; "(|= flags mask)" ]);
  Harness.test "loops and their clauses" (fun () ->
      Parse_support.expect_statement
        "while low < high\n  invariant high <= length\n  decreases high - low, 1\n{\n  todo\n}"
        "(while (< low high) (invariant (<= high length)) (decreases (- high low) 1) (block todo))";
      Parse_support.expect_statement "for (index, element) in mut scores.enumerate() {}"
        "(for (record index element) (mut (call (. scores enumerate))) (block))";
      Parse_support.expect_statement "parallel for player in mut players {}"
        "(parallel-for player (mut players) (block))";
      Parse_support.expect_statement "concurrent for message in receiver.messages() {}"
        "(concurrent-for message (call (. receiver messages)) (block))";
      Parse_support.expect_statement "for index: UInt8 in 0..10 {}"
        "(for index : UInt8 (.. 0 10) (block))";
      Parse_support.expect_statement "for (index, element): Indexed[UInt8] in data.enumerate() {}"
        "(for (record index element) : Indexed[UInt8] (call (. data enumerate)) (block))");
  Harness.test "a loop has at most one decreases" (fun () ->
      Parse_support.expect_body_error "while a\n  decreases b\n  decreases c\n{}"
        ~code:Repeated_clause ~at:"decreases c");
  Harness.test "parallel, concurrent, and proof" (fun () ->
      Parse_support.expect_statement "parallel {\n  let a = 1\n  let b = 2\n}"
        "(parallel (block (let a 1) (let b 2)))";
      Parse_support.expect_statement "concurrent {\n  let a = f()\n  g()\n}"
        "(concurrent (block (let a (call f)) (call g)))";
      Parse_support.expect_statement "proof {\n  lemma()\n}" "(proof (block (call lemma)))");
  Harness.test "a match arm's body is a statement" (fun () ->
      Parse_support.expect_statement
        "match event {\n  Click => clicks += 1\n  Done =>\n    finish()\n}"
        "(match (event) (=> Click (+= clicks 1)) (=> Done (call finish)))")

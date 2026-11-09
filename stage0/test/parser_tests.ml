(* The parser's tests. Each test gives an input and states exactly what the
   parser must do with it: the tree, printed compactly, or the one
   diagnostic with its code, position, and fixes. See IMPLEMENTATION.md,
   "Testing", and PARSER.md, "Testing". *)

(* Running tests *)

let failures = ref 0
let count = ref 0
let current_test = ref ""

let fail format =
  Printf.ksprintf
    (fun message ->
      incr failures;
      Printf.printf "FAIL %s: %s\n" !current_test message)
    format

let test name body =
  incr count;
  current_test := name;
  match body () with
  | () -> ()
  | exception exception_ -> fail "raised %s" (Printexc.to_string exception_)

(* Parsing *)

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

(* Asserts that [text] parses with no diagnostics into definitions that
   print as [expected]. *)
let definitions text expected =
  let file, diagnostics = parse text in
  no_diagnostics text diagnostics;
  let actual =
    List.map
      (fun (item : Syntax.definition Syntax.item) -> Syntax_print.definition item.value)
      file.definitions
  in
  if actual <> expected then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)

let definition text expected = definitions text [ expected ]

(* The statements of a function's body. *)
let body_of text =
  let file, diagnostics = parse ("fn example() {\n" ^ text ^ "\n}") in
  match file.definitions with
  | [ { value = { kind = Function { body; _ }; _ }; _ } ] -> (body.statements, diagnostics)
  | _ -> ([], diagnostics)

(* Asserts that [text], as the body of a function, parses with no
   diagnostics into statements that print as [expected]. *)
let statements text expected =
  let statements, diagnostics = body_of text in
  no_diagnostics text diagnostics;
  let actual = List.map Syntax_print.statement statements in
  if actual <> expected then
    fail "expected [%s], got [%s]" (String.concat "; " expected) (String.concat "; " actual)

let statement text expected = statements text [ expected ]
let find = Documents.find

(* Asserts that [text] gives exactly one diagnostic, with [code], starting at
   the [occurrence]th occurrence of [at]. With [fixed], its fixes must turn
   [text] into [fixed] and then [alternatives], each of which must parse
   with no diagnostics. Without [fixed], it must have no fix. *)
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
      let expected = find text at ~occurrence in
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

(* An error in a function's body. *)
let body_error ?fixed ?alternatives ?occurrence text ~code ~at =
  let wrap text = "fn example() {\n" ^ text ^ "\n}" in
  error ?fixed:(Option.map wrap fixed)
    ?alternatives:(Option.map (List.map wrap) alternatives)
    ?occurrence (wrap text) ~code ~at

(* Splitting a file into definitions *)

let () =
  test "definitions are split at line breaks outside brackets" (fun () ->
      definitions "fn first() {}\nfn second() {}"
        [ "(fn first () (block))"; "(fn second () (block))" ]);
  test "a body on the next line stays with its signature" (fun () ->
      definition "fn first()\n  uses Clock\n{\n  todo\n}" "(fn first () (uses Clock) (block todo))");
  test "use lines are kept apart from definitions" (fun () ->
      let file, diagnostics =
        parse "use standard::json\nuse weather::forecast::hourly\nfn f() {}"
      in
      no_diagnostics "" diagnostics;
      if
        List.map (fun (item : Syntax.path Syntax.item) -> Syntax_print.path item.value) file.uses
        <> [ "standard::json"; "weather::forecast::hourly" ]
      then fail "wrong use lines");
  test "a use line after a definition moves up" (fun () ->
      error "use a::b\n\nfn f() {}\nuse c::d\n" ~code:Use_after_definition ~at:"use c::d"
        ~fixed:"use a::b\nuse c::d\n\nfn f() {}\n");
  test "a use line after the first definition moves above it" (fun () ->
      error "fn f() {}\nuse c::d\n" ~code:Use_after_definition ~at:"use c::d"
        ~fixed:"use c::d\nfn f() {}\n");
  test "a statement at the top level is one error" (fun () ->
      error "fn f() {}\nx = 1\nfn g() {}" ~code:Statement_at_top_level ~at:"x");
  test "the definition after a broken one parses" (fun () ->
      let file, diagnostics = parse "fn f() -> {\n}\nfn g() {}" in
      if List.length diagnostics <> 1 then
        fail "expected one diagnostic, got [%s]" (String.concat "; " (codes diagnostics));
      match file.definitions with
      | [ _; { value = { kind = Function _; _ }; _ } ] -> ()
      | _ -> fail "g did not parse");
  test "a missing } does not swallow the next definition" (fun () ->
      let file, diagnostics = parse "fn f() {\n  todo\nfn g() {}" in
      if codes diagnostics <> [ "lexer.unclosed_bracket" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      if List.length file.definitions <> 2 then fail "expected two definitions")

(* Parsing one definition *)

let () =
  test "spans are relative to the definition" (fun () ->
      match (fst (parse "fn f() {}\n\nfn g() {}")).definitions with
      | [ _; second ] ->
          if second.base <> 11 then fail "base %d" second.base;
          if second.value.span.start <> 0 || second.value.span.stop <> 9 then fail "span";
          if second.text <> "fn g() {}" then fail "text %S" second.text;
          if not second.blank_line_before then fail "blank line"
      | _ -> fail "expected two definitions");
  test "moving a definition changes nothing in its tree" (fun () ->
      let text =
        "fn f(items: List[Int64]) -> Int64 {\n\
        \  let total = \"${items.length()}\"\n\
        \  items[0] + 1\n\
         }"
      in
      match
        ((fst (parse text)).definitions, (fst (parse ("fn g() {}\n\n\n" ^ text))).definitions)
      with
      | [ alone ], [ _; moved ] -> if alone.value <> moved.value then fail "the trees differ"
      | _ -> fail "wrong definitions");
  test "interpolations are parsed with the definition's base" (fun () ->
      match (fst (parse "fn g() {}\nfn f() { \"${x + 1}\" }")).definitions with
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
         _;
       };
      ] ->
          if value.span.start <> 12 then fail "interpolation span %d" value.span.start
      | _ -> fail "wrong tree");
  test "nesting deeper than the limit is one error" (fun () ->
      let text = "fn f() { " ^ String.make 300 '(' ^ "1" ^ String.make 300 ')' ^ " }" in
      if codes (snd (parse text)) <> [ "parser.nesting_too_deep" ] then
        fail "got [%s]" (String.concat "; " (codes (snd (parse text)))))

let () =
  let deep text = List.filter (( = ) "parser.nesting_too_deep") (codes (snd (parse text))) in
  test "nested echo counts toward the limit" (fun () ->
      let text =
        "fn f() {\n  let x = " ^ String.concat "" (List.init 300 (fun _ -> "echo ")) ^ "1\n}"
      in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "nested if counts toward the limit" (fun () ->
      let text =
        "fn f() {\n  let x = "
        ^ String.concat "" (List.init 300 (fun _ -> "if "))
        ^ "x"
        ^ String.concat "" (List.init 300 (fun _ -> " {}"))
        ^ "\n}"
      in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "an inner statement cut off by an inserted closer leaves the outer one reported" (fun () ->
      let _, diagnostics = parse "fn f() {\n  let x = run(fn() { g( }) +\n}" in
      if codes diagnostics <> [ "lexer.unclosed_bracket"; "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)))

(* Parsing one piece at a time *)

let () =
  let pieces text =
    let source = source text in
    let tokens, _ = Lexer.lex source in
    (source, tokens, Parser.split tokens)
  in
  test "a definition's diagnostics are placed in the file by its base" (fun () ->
      match pieces "fn g() {}\nfn f() { x = }" with
      | source, tokens, [ _; second ] -> (
          let parsed = Parser.definition source tokens second in
          match Parser.placed parsed with
          | [ diagnostic ] ->
              if diagnostic.span.start <> 23 then fail "start %d" diagnostic.span.start
          | _ -> fail "expected one diagnostic")
      | _ -> fail "expected two pieces");
  test "moving a definition changes neither its tree nor its diagnostics" (fun () ->
      let text = "fn f(items: List[Int64]) {\n  let total = items[0] +\n}" in
      let parsed text =
        let source, tokens, pieces = pieces text in
        let last = List.nth pieces (List.length pieces - 1) in
        let parsed = Parser.definition source tokens last in
        (parsed.value.value, parsed.diagnostics)
      in
      if parsed text <> parsed ("fn g() {}\n\n\n" ^ text) then fail "the results differ")

(* Types *)

let () =
  let type_of text expected =
    definition ("fn f(value: " ^ text ^ ") {}") ("(fn f ((value: " ^ expected ^ ")) (block))")
  in
  test "a path type with arguments" (fun () ->
      type_of "standard::json::Map[String, List[Int64]]" "standard::json::Map[String, List[Int64]]");
  test "a count argument and a count parameter" (fun () ->
      type_of "Array[UInt8, 32]" "Array[UInt8, 32]";
      type_of "Array[Int64, count]" "Array[Int64, count]");
  test "Self and its associated types" (fun () ->
      type_of "Self" "Self";
      type_of "Self.Key" "Self.Key");
  test "an associated type of a parameter" (fun () -> type_of "Items.Element" "Items.Element");
  test "any with a constraint" (fun () ->
      type_of "any Cursor[Element = Int64]" "(any Cursor[Element = Int64])");
  test "a function type" (fun () ->
      type_of "fn(mut Element, Element) -> Ordering" "(fn (mut Element Element) -> Ordering)");
  test "a function type in parentheses with clauses" (fun () ->
      type_of "(fn(Item) uses Clock, Random cost time finite)"
        "(fn (Item) (uses Clock Random) (cost time finite))");
  test "parentheses around a function type need clauses" (fun () ->
      error "fn f(value: (fn(Item))) {}" ~code:Unexpected_token ~at:"(fn");
  test "requires in a function type" (fun () ->
      error "fn f(value: (fn(Item) requires true)) {}" ~code:Unexpected_token ~at:"requires");
  test "generic parameters" (fun () ->
      definition "fn f[Key: Hash + Ordered, count: USize, capability Granted]() {}"
        "(fn f[Key: Hash + Ordered, count: USize, capability Granted] () (block))")

(* Patterns *)

let () =
  let pattern_of text expected =
    statement ("let " ^ text ^ " = value") ("(let " ^ expected ^ " value)")
  in
  let arm_of text expected =
    statement
      ("match value {\n  " ^ text ^ " => todo\n}")
      ("(match (value) (=> " ^ expected ^ " todo))")
  in
  test "a binding or constant" (fun () -> pattern_of "name" "name");
  test "a wildcard" (fun () -> pattern_of "_" "_");
  test "a record pattern" (fun () ->
      pattern_of "(index, element: score, ..)" "(record index (element: score) ..)");
  test "a variant pattern" (fun () -> arm_of "Some(Circle(radius, ..))" "(Some (Circle radius ..))");
  test "a variant from a module" (fun () -> arm_of "geometry::Empty" "geometry::Empty");
  test "qualified constants" (fun () ->
      arm_of "http::ok" "http::ok";
      arm_of "Status.teapot" "Status.teapot");
  test "literals" (fun () ->
      arm_of "-1" "-1";
      arm_of "\"GET\"" "\"GET\"";
      arm_of "Character\"a\"" "Character\"a\"");
  test "alternatives" (fun () -> arm_of "301 | 302 | Low" "(| 301 302 Low)");
  test "ranges" (fun () ->
      arm_of "500..=599" "(..= 500 599)";
      arm_of "0..=max_port" "(..= 0 max_port)";
      arm_of "UInt16.minimum..=UInt16.maximum" "(..= UInt16.minimum UInt16.maximum)";
      arm_of "Character\"a\"..=Character\"z\"" "(..= Character\"a\" Character\"z\")");
  test "a guard" (fun () -> arm_of "code if code >= 400" "code (if (>= code 400))");
  test "several values" (fun () ->
      statement "match state, event {\n  Idle | Paused, Tick => todo\n}"
        "(match (state event) (=> (| Idle Paused) Tick todo))");
  test ".. must be the last field" (fun () ->
      body_error "let (.., x) = value" ~code:Unexpected_token ~at:"..");
  test "a float literal is not a pattern" (fun () ->
      body_error "match x {\n  0.0 => todo\n}" ~code:Float_pattern ~at:"0.0");
  test "a range pattern needs both ends" (fun () ->
      body_error "match x {\n  0.. => todo\n}" ~code:Unexpected_token ~at:"=>");
  test "a string in a pattern cannot interpolate" (fun () ->
      body_error "match x {\n  \"${y}\" => todo\n}" ~code:Interpolation_not_allowed ~at:"\"${")

(* Expressions *)

let () =
  let expression text expected = statement ("let x = " ^ text) ("(let x " ^ expected ^ ")") in
  test "arithmetic precedence" (fun () -> expression "a + b * c - d" "(- (+ a (* b c)) d)");
  test "prefix binds tighter than infix" (fun () ->
      expression "-x.abs() + !ready" "(+ (- (call (. x abs))) (! ready))");
  test "ranges bind more loosely than arithmetic" (fun () ->
      expression "0..count - 1" "(.. 0 (- count 1))");
  test "comparison and logic" (fun () ->
      expression "a < b && c is Some(d)" "(&& (< a b) (is c (Some d)))");
  test "implication binds most loosely" (fun () ->
      definition "fn f() requires a && b ==> c || d {}"
        "(fn f () (requires (==> (&& a b) (|| c d))) (block))");
  test "postfix operators" (fun () ->
      expression "a.b[0](c, label: d)?.e with (f.g: 1, h)"
        "(with (. (? (call ([] (. a b) 0) c (label: d))) e) (f.g: 1) h)");
  test "modes and any take a postfix expression" (fun () ->
      statement "mut config.servers.sort()" "(mut (call (. (. config servers) sort)))";
      expression "any UserRoutes(users: [:])" "(any (call UserRoutes (users: (map))))");
  test "own with an update" (fun () ->
      expression "own config with (debug: true)" "(own (with config (debug: true)))");
  test "open ranges in brackets" (fun () ->
      expression "items[2..]" "([] items (.. 2 _))";
      expression "items[..3]" "([] items (.. _ 3))";
      expression "items[..=3]" "([] items (..= _ 3))");
  test "an open range outside brackets" (fun () ->
      body_error "for i in 0.. {}" ~code:Open_range ~at:"..");
  test "an open start outside brackets" (fun () ->
      body_error "let x = ..3" ~code:Open_range ~at:"..");
  test "an open range is alone in its brackets" (fun () ->
      body_error "let x = items[1.., 4]" ~code:Open_range ~at:"..");
  test "a lambda's body may start on the next line" (fun () ->
      statement "let f: fn(Job) -> Bool = fn(job)\n{\n  job.ready\n}"
        "(let f : (fn (Job) -> Bool) (fn (job) (block (. job ready))))");
  test "as at the end of a line is not read with the next line" (fun () ->
      body_error "let n = size as\nlet m = 1" ~code:Reserved_word ~at:"as");
  test "brackets cannot be empty" (fun () ->
      body_error "let x = items[]" ~code:Unexpected_token ~at:"]");
  test "i++ is recognized only at the end of a line" (fun () ->
      body_error "count++ x" ~code:Unexpected_token ~at:"++");
  test "type arguments and constraints in brackets" (fun () ->
      expression "List[String].with_capacity(64)" "(call (. ([] List String) with_capacity) 64)";
      expression "total[Iterable[Element = Int64]]" "([] total ([] Iterable Element = Int64))");
  test "a collection cannot mix list elements and map entries" (fun () ->
      body_error "let x = [1, \"a\": 2]" ~code:Unexpected_token ~at:"\"a\"";
      body_error "let x = [\"a\": 1, 2]" ~code:Unexpected_token ~at:"2]");
  test "a field and an update that do not parse are errors in the tree" (fun () ->
      let file, _ = parse "type T(x: Int64, 1)" in
      (match file.definitions with
      | [ { value; _ } ] ->
          if Syntax_print.definition value <> "(type T ((x: Int64) error))" then
            fail "got %s" (Syntax_print.definition value)
      | _ -> fail "wrong definitions");
      let statements, _ = body_of "let y = x with (1)" in
      if List.map Syntax_print.statement statements <> [ "(let y (with x error))" ] then
        fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "lists and maps" (fun () ->
      expression "[1, 2,]" "(list 1 2)";
      expression "[]" "(list)";
      expression "[\"http\": 80, name: 1]" "(map (\"http\" 80) (name 1))";
      expression "[:]" "(map)");
  test "a lambda" (fun () ->
      expression "fn(sum, (value, ..)) { sum + value }"
        "(fn (sum (record value ..)) (block (+ sum value)))");
  test "if, else if, and else" (fun () ->
      expression "if a { 1 } else if b { 2 } else { 3 }"
        "(if a (block 1) (if b (block 2) (block 3)))");
  test "provide" (fun () ->
      expression "provide mut files, DiscardLog() { run() }"
        "(provide ((mut files) (call DiscardLog)) (block (call run)))");
  test "a block" (fun () -> expression "{\n  let y = 1\n  y\n}" "(block (let y 1) y)");
  test "return with and without a value" (fun () ->
      statement "return" "(return)";
      statement "return { 1 }" "(return (block 1))";
      statements "if a { return }\nb" [ "(if a (block (return)))"; "b" ]);
  test "echo takes everything after it" (fun () ->
      expression "echo player.wins * 3" "(echo (* (. player wins) 3))");
  test "strings, tagged strings, and interpolations" (fun () ->
      expression "\"a${b + 1}c\"" "\"a${(+ b 1)}c\"";
      expression "database::SqlQuery\"select ${id}\"" "database::SqlQuery\"select ${id}\"";
      expression "\"${names.join(\", \")}\"" "\"${(call (. names join) \", \")}\"");
  test "nothing more is reported at the end of an interpolation a line break cut off" (fun () ->
      let _, diagnostics = parse "fn f() {\n  let x = \"\"\"a ${b ? c\n  \"\"\"\n}" in
      if
        List.filter (fun code -> String.starts_with ~prefix:"parser." code) (codes diagnostics)
        <> []
      then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "an error in an interpolation stays there" (fun () ->
      let statements, diagnostics = body_of "let x = \"${a +}\"\nlet y = 1" in
      if codes diagnostics <> [ "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      if List.length statements <> 2 then fail "expected two statements");
  test "constants and names" (fun () ->
      expression "true" "true";
      expression "Self.Key" "(. Self Key)";
      expression "geometry::Shape.Circle" "(. geometry::Shape Circle)";
      expression "json::parse" "json::parse");
  test "quantifiers in a specification" (fun () ->
      definition "fn f() requires count > 0 && forall i in 0..count => items[i] > 0 || done {}"
        "(fn f () (requires (&& (> count 0) (forall (in i (.. 0 count)) (|| (> ([] items i) 0) \
         done)))) (block))";
      definition "fn f() requires forall value: Int64 => value + 0 == value {}"
        "(fn f () (requires (forall value: Int64 (== (+ value 0) value))) (block))")

(* Statements *)

let () =
  test "let and var with annotations" (fun () ->
      statements "let a: Int64 = 1\nvar (low, high) = bounds"
        [ "(let a : Int64 1)"; "(var (record low high) bounds)" ]);
  test "let ... else" (fun () ->
      statement "let Some(user) = find(id) else {\n  return\n}"
        "(let (Some user) (call find id) (else (block (return))))");
  test "the expression before let ... else cannot end with }" (fun () ->
      body_error "let Some(x) = if ready { a } else { b } else { return }" ~code:Let_else_brace
        ~at:"else { return" ~fixed:"let Some(x) = (if ready { a } else { b }) else { return }");
  test "assignments" (fun () ->
      statements "a = 1\nitems[i] += 2\nflags |= mask"
        [ "(= a 1)"; "(+= ([] items i) 2)"; "(|= flags mask)" ]);
  test "loops and their clauses" (fun () ->
      statement
        "while low < high\n  invariant high <= length\n  decreases high - low, 1\n{\n  todo\n}"
        "(while (< low high) (invariant (<= high length)) (decreases (- high low) 1) (block todo))";
      statement "for (index, element) in mut scores.enumerate() {}"
        "(for (record index element) (mut (call (. scores enumerate))) (block))";
      statement "parallel for player in mut players {}"
        "(parallel-for player (mut players) (block))");
  test "a loop has at most one decreases" (fun () ->
      body_error "while a\n  decreases b\n  decreases c\n{}" ~code:Repeated_clause ~at:"decreases c");
  test "parallel, proof, and yield" (fun () ->
      statement "parallel {\n  let a = 1\n  let b = 2\n}" "(parallel (block (let a 1) (let b 2)))";
      statement "proof {\n  lemma()\n}" "(proof (block (call lemma)))");
  test "a match arm's body is a statement" (fun () ->
      statement "match event {\n  Click => clicks += 1\n  Done =>\n    finish()\n}"
        "(match (event) (=> Click (+= clicks 1)) (=> Done (call finish)))")

(* Definitions *)

let () =
  test "a method, its receiver, and its result" (fun () ->
      definition
        "fn List[Element: Ordered].sort(mut self, by: Order = Order.Ascending) yields mut Element \
         {}"
        "(fn List[Element: Ordered].sort (mut self (by: Order (= (. Order Ascending)))) yields mut \
         Element (block))";
      definition "fn hourly::Forecast.summary(self) -> String { todo }"
        "(fn hourly::Forecast.summary (self) -> String (block todo))");
  test "clauses in the order written" (fun () ->
      definition
        "fn f(x: Int64) -> Int64\n\
        \  ensures result > x\n\
        \  requires x > 0\n\
        \  decreases x, 1\n\
        \  uses Clock\n\
         {\n\
        \  x\n\
         }"
        "(fn f ((x: Int64)) -> Int64 (ensures (> result x)) (requires (> x 0)) (decreases x 1) \
         (uses Clock) (block x))");
  test "cost clauses" (fun () ->
      definition
        "fn f(visit: (fn(Item) cost time finite))\n\
        \  cost amortized time O(items.length() * time(visit))\n\
        \  cost allocations <= 1\n\
        \  cost calls(visit) == 2\n\
        \  cost calls(FileRead.read) == 3\n\
        \  cost calls(FileRead) == 4\n\
        \  cost time finite\n\
         {}"
        "(fn f ((visit: (fn (Item) (cost time finite)))) (cost amortized time (O (* (call (. items \
         length)) (call time visit)))) (cost allocations (<= 1)) (cost (calls visit) (== 2)) (cost \
         (calls FileRead.read) (== 3)) (cost (calls FileRead) (== 4)) (cost time finite) (block))");
  test "parsing goes on after a misspelled cost word" (fun () ->
      error "fn f() cost time fnite {}" ~code:Cost_word ~at:"fnite"
        ~fixed:"fn f() cost time finite {}";
      let _, diagnostics = parse "fn f() cost tme fnite {}" in
      if codes diagnostics <> [ "parser.cost_word"; "parser.cost_word" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a trait's body on the next line" (fun () ->
      definition "trait T\n{\n  type K\n}" "(trait T (type K))");
  test "a misspelled cost word has a fix" (fun () ->
      error "fn f() cost allocation == 0 {}" ~code:Cost_word ~at:"allocation"
        ~fixed:"fn f() cost allocations == 0 {}");
  test "finite is only for time" (fun () ->
      error "fn f() cost allocations finite {}" ~code:Finite_not_time ~at:"finite");
  test "cost potential belongs to a type" (fun () ->
      error "fn f() cost potential x {}" ~code:Misplaced_potential ~at:"potential");
  test "uses appears at most once" (fun () ->
      error "fn f() uses Clock uses Random {}" ~code:Repeated_clause ~at:"uses Random");
  test "a missing body gets { todo }" (fun () ->
      error "fn f() -> Int64\nfn g() {}" ~code:Missing_body ~at:"\nfn g"
        ~fixed:"fn f() -> Int64 {\n  todo\n}\nfn g() {}");
  test "a missing body after a visibility is not indented" (fun () ->
      error "public fn f()\nfn g() {}" ~code:Missing_body ~at:"\nfn g"
        ~fixed:"public fn f() {\n  todo\n}\nfn g() {}");
  test "self only in a method" (fun () -> error "fn f(self) {}" ~code:Misplaced_self ~at:"self");
  test "self only first" (fun () ->
      error "fn T.f(x: Int64, self) {}" ~code:Misplaced_self ~at:"self");
  test "a parameter cannot be named result" (fun () ->
      error "fn f(result: Int64) {}" ~code:Reserved_name ~at:"result");
  test "a function cannot be named old" (fun () ->
      error "fn old() {}" ~code:Reserved_name ~at:"old");
  test "types" (fun () ->
      definition "type Point(x: Float64, y: Float64 = 0.0)"
        "(type Point ((x: Float64) (y: Float64 (= 0e0))))";
      definition "type DiscardLog()" "(type DiscardLog ())";
      definition "type Bit = Zero | One" "(type Bit (= Zero One))";
      definition "public opaque type Session = todo" "(public opaque (type Session = todo))";
      definition
        "type Tree[Value] =\n\
        \  | Leaf\n\
        \  | indirect Node(left: Tree[Value], right: Tree[Value])\n\
        \  invariant is_balanced(self)\n\
        \  derives Equal, Hash\n\
        \  cost potential size(self)"
        "(type Tree[Value] (= Leaf (indirect Node ((left: Tree[Value]) (right: Tree[Value])))) \
         (invariant (call is_balanced self)) (derives Equal Hash) (cost potential (call size \
         self)))");
  test "a trait" (fun () ->
      definition
        "trait Ordered: Equal {\n\
        \  type Key: Hash\n\
        \  fn compare(self, other: Self) -> Ordering\n\
        \  fn max(own self, other: own Self) -> Self\n\
        \    ensures true\n\
        \  {\n\
        \    self\n\
        \  }\n\n\
        \  law transitive(a: Self, b: Self)\n\
        \    requires a <= b\n\
        \  {\n\
        \    true\n\
        \  }\n\
         }"
        "(trait Ordered : Equal (type Key: Hash) (fn compare (self (other: Self)) -> Ordering) (fn \
         max (own self (other: own Self)) -> Self (ensures true) (block self)) (law transitive \
         ((a: Self) (b: Self)) (requires (<= a b)) (block true)))";
      definition "trait Loggable: Display + Hash {}" "(trait Loggable : Display + Hash)");
  test "an impl" (fun () ->
      definition
        "impl FileRead for FilesWithin\n\
        \  uses FileRead\n\
         {\n\
        \  type Error = FileError\n\
        \  fn read(self) -> Bytes { todo }\n\
         }"
        "(impl FileRead for FilesWithin (uses FileRead) (type Error = FileError) (fn read (self) \
         -> Bytes (block todo)))";
      definition "impl Display for List[Element: Display] {}"
        "(impl Display for List[Element: Display])");
  test "a capability" (fun () ->
      definition "capability Clock {\n  fn now() -> Instant\n  fn sleep(duration: Duration)\n}"
        "(capability Clock (fn now () -> Instant) (fn sleep ((duration: Duration))))");
  test "a capability's methods take no self" (fun () ->
      error "capability Clock {\n  fn now(self) -> Instant\n}" ~code:Misplaced_self ~at:"self");
  test "an impl's methods need bodies" (fun () ->
      error "impl Clock for Fixed {\n  fn now(self) -> Instant\n}" ~code:Missing_body ~at:"\n}"
        ~fixed:"impl Clock for Fixed {\n  fn now(self) -> Instant {\n    todo\n  }\n}");
  test "constants" (fun () ->
      definition "public let UInt8.maximum: UInt8 = 255" "(public (let UInt8.maximum : UInt8 255))";
      definition "let pi: Float64 = 3.14" "(let pi : Float64 314e-2)");
  test "a test, a theorem, and a law's proof" (fun () ->
      definition "test \"writes\"\n  uses FileWrite\n{\n  assert true\n}"
        "(test \"writes\" (uses FileWrite) (block (assert true)))";
      definition "public theorem keeps[Element](items: List[Element])\n  ensures true\n{\n}"
        "(public (theorem keeps[Element] ((items: List[Element])) (ensures true) (block)))";
      definition "proof Monoid.associative for Int64 {\n  lemma()\n}"
        "(proof Monoid.associative for Int64 (block (call lemma)))");
  test "a test's name is a plain string" (fun () ->
      error "test \"a${b}\" {}" ~code:Interpolation_not_allowed ~at:"\"a");
  test "an impl takes no visibility" (fun () ->
      error "public impl A for B {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:"impl A for B {}");
  test "a test takes no visibility" (fun () ->
      error "internal test \"a\" {}" ~code:Misplaced_visibility ~at:"internal"
        ~fixed:"test \"a\" {}");
  test "a law's proof takes no visibility" (fun () ->
      error "public proof A.b for C {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:"proof A.b for C {}");
  test "only a type is opaque" (fun () ->
      error "public opaque fn f() {}" ~code:Misplaced_opaque ~at:"opaque" ~fixed:"public fn f() {}")

(* Precedence and combinations that need parentheses *)

let () =
  (* The error points at [at], the operator that cannot take its operand. *)
  let combination text ~at ~code ~fixes =
    match fixes with
    | fixed :: alternatives ->
        body_error ("let x = " ^ text) ~code ~at ~fixed:("let x = " ^ fixed)
          ~alternatives:(List.map (( ^ ) "let x = ") alternatives)
    | [] -> body_error ("let x = " ^ text) ~code ~at
  in
  test "bitwise and comparison: Rust's reading, then C's" (fun () ->
      combination "flags & mask == 0" ~at:"==" ~code:Needs_parentheses
        ~fixes:[ "(flags & mask) == 0"; "flags & (mask == 0)" ]);
  test "shift and addition: C and Rust's reading, then Go and Swift's" (fun () ->
      combination "a << b + 1" ~at:"<<" ~code:Needs_parentheses
        ~fixes:[ "a << (b + 1)"; "(a << b) + 1" ]);
  test "& and | read the same everywhere" (fun () ->
      combination "a & b | c" ~at:"|" ~code:Needs_parentheses ~fixes:[ "(a & b) | c" ]);
  test "& and | read the same on the right" (fun () ->
      combination "c | a & b" ~at:"|" ~code:Needs_parentheses ~fixes:[ "c | (a & b)" ]);
  test "a reading that needs more parentheses inside && gets them" (fun () ->
      combination "a & b == c && d" ~at:"==" ~code:Needs_parentheses
        ~fixes:[ "(a & b) == c && d"; "(a & (b == c)) && d" ]);
  test "the other reading takes the operand next to the operator" (fun () ->
      combination "s & a + b + c" ~at:"&" ~code:Needs_parentheses
        ~fixes:[ "s & (a + b + c)"; "(s & a) + b + c" ]);
  test "the same bitwise operator chains" (fun () ->
      statement "let x = a | b | c" "(let x (| (| a b) c))");
  test "shifts chain" (fun () -> statement "let x = a << 1 >> 2" "(let x (>> (<< a 1) 2))");
  test "&& and || cannot be mixed" (fun () ->
      combination "a && b || c" ~at:"||" ~code:Needs_parentheses
        ~fixes:[ "(a && b) || c"; "a && (b || c)" ]);
  test "comparisons do not chain" (fun () ->
      combination "a < b < c" ~at:"< c" ~code:Needs_parentheses ~fixes:[ "a < b && b < c" ]);
  test "a chained comparison without a simple middle has no fix" (fun () ->
      combination "a < f(b) < c" ~at:"< c" ~code:Needs_parentheses ~fixes:[]);
  test "is does not chain" (fun () ->
      combination "a is B == c" ~at:"==" ~code:Needs_parentheses ~fixes:[]);
  test "ranges do not chain" (fun () ->
      combination "0..10..20" ~at:"..20" ~code:Needs_parentheses ~fixes:[]);
  test "==> does not chain: Dafny's reading first" (fun () ->
      error "fn f() requires a ==> b ==> c {}" ~code:Needs_parentheses ~at:"==> c"
        ~fixed:"fn f() requires a ==> (b ==> c) {}"
        ~alternatives:[ "fn f() requires (a ==> b) ==> c {}" ]);
  test "parentheses settle a combination" (fun () ->
      statement "let x = (flags & mask) == 0" "(let x (== (paren (& flags mask)) 0))");
  test "a quantifier may end && in a specification" (fun () ->
      definition "fn f() requires a && exists x in s => x {}"
        "(fn f () (requires (&& a (exists (in x s) x))) (block))");
  test "a quantifier elsewhere needs parentheses" (fun () ->
      error "fn f() requires count + forall x in s => x {}" ~code:Needs_parentheses ~at:"forall"
        ~fixed:"fn f() requires count + (forall x in s => x) {}");
  test "echo as an operand needs parentheses" (fun () ->
      body_error "let x = count + echo x" ~code:Needs_parentheses ~at:"echo"
        ~fixed:"let x = count + (echo x)");
  test "each combination in a chain is reported" (fun () ->
      let _, diagnostics = body_of "let x = a < b < c < d" in
      if List.length diagnostics <> 2 then fail "got %d diagnostics" (List.length diagnostics))

(* Checks on a whole definition *)

let () =
  test "forall outside a specification" (fun () ->
      body_error "let x = forall i in s => i" ~code:Specification_only ~at:"forall");
  test "==> outside a specification" (fun () ->
      body_error "let x = a ==> b" ~code:Specification_only ~at:"==>");
  test "specifications allow forall" (fun () ->
      definition "type S(items: List[Int64])\n  invariant forall i in items => i > 0"
        "(type S ((items: List[Int64])) (invariant (forall (in i items) (> i 0))))";
      statement "while a\n  invariant forall i in s => i\n{}"
        "(while a (invariant (forall (in i s) i)) (block))");
  test "assert outside tests and proofs" (fun () ->
      body_error "assert true" ~code:Misplaced_assert ~at:"assert");
  test "assert in a proof block" (fun () ->
      statement "proof {\n  assert true\n}" "(proof (block (assert true)))");
  test "assert in a lambda in a test" (fun () ->
      error "test \"a\" {\n  run(fn(x) { assert x })\n}" ~code:Misplaced_assert ~at:"assert");
  test "a proof block outside a function's body" (fun () ->
      error "test \"a\" {\n  proof {}\n}" ~code:Misplaced_proof ~at:"proof");
  test "yield only in a method that yields" (fun () ->
      body_error "yield 1" ~code:Misplaced_yield ~at:"yield";
      definition "fn T.each(self) yields Int64 {\n  yield 1\n}"
        "(fn T.each (self) yields Int64 (block (yield 1)))");
  test "a method that lends" (fun () ->
      definition
        "fn Grid.cell(mut self, position: Position) lends mut Cell {\n  yield mut self.cells[0]\n}"
        "(fn Grid.cell (mut self (position: Position)) lends mut Cell (block (yield (mut ([] (. \
         self cells) 0)))))");
  test "lends own" (fun () ->
      error "fn T.part(own self) lends own Part {}" ~code:Lends_own ~at:"own Part"
        ~fixed:"fn T.part(own self) lends Part {}");
  test "yield in a lambda" (fun () ->
      error "fn T.each(self) yields Int64 {\n  f(fn() { yield 1 })\n}" ~code:Misplaced_yield
        ~at:"yield 1");
  test "break outside a loop" (fun () -> body_error "break" ~code:Misplaced_loop_exit ~at:"break");
  test "continue across a lambda" (fun () ->
      body_error "for x in s {\n  f(fn() { continue })\n}" ~code:Misplaced_loop_exit ~at:"continue");
  test "break and continue in a loop" (fun () ->
      statement "while true {\n  if a { break } else { continue }\n}"
        "(while true (block (if a (block break) (block continue))))");
  test "return leaving a parallel block" (fun () ->
      body_error "parallel {\n  return\n}" ~code:Leaves_parallel ~at:"return");
  test "? leaving a parallel for" (fun () ->
      body_error "parallel for x in s {\n  let y = f(x)?\n}" ~code:Leaves_parallel ~at:"?");
  test "break in a parallel for" (fun () ->
      body_error "parallel for x in s {\n  break\n}" ~code:Leaves_parallel ~at:"break");
  test "continue in a parallel for" (fun () ->
      statement "parallel for x in s {\n  continue\n}" "(parallel-for x s (block continue))");
  test "break leaving a branch" (fun () ->
      body_error "while a {\n  parallel {\n    break\n  }\n}" ~code:Leaves_parallel ~at:"break");
  test "a loop inside a branch" (fun () ->
      statement "parallel {\n  for x in s { break }\n}" "(parallel (block (for x s (block break))))");
  test "return in a lambda inside a branch" (fun () ->
      statement "parallel {\n  f(fn() { return })\n}"
        "(parallel (block (call f (fn () (block (return))))))");
  test "echo in a specification" (fun () ->
      error "fn f(x: Int64) requires echo x > 0 {}" ~code:Echo_in_specification ~at:"echo");
  test "a statement rule applies in every block" (fun () ->
      body_error "let x = provide Fixed() {\n  assert true\n}" ~code:Misplaced_assert ~at:"assert");
  test "echo in a proof" (fun () ->
      body_error "proof {\n  echo x\n}" ~code:Echo_in_specification ~at:"echo")

(* Recovery *)

let () =
  test "an error in a statement leaves the next one parsed" (fun () ->
      let statements, diagnostics = body_of "let x = 1 2 3\nlet y = 2" in
      if codes diagnostics <> [ "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      if List.map Syntax_print.statement statements <> [ "error"; "(let y 2)" ] then
        fail "wrong statements");
  test "each bad item in brackets gets its own error" (fun () ->
      let statements, diagnostics = body_of "f(1 +, x, 2 3, g(a b))\nlet y = 2" in
      if
        codes diagnostics
        <> [ "parser.unexpected_token"; "parser.unexpected_token"; "parser.unexpected_token" ]
      then fail "got [%s]" (String.concat "; " (codes diagnostics));
      if
        List.map Syntax_print.statement statements
        <> [ "(call f error x error (call g error))"; "(let y 2)" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "an error in a clause leaves the body parsed" (fun () ->
      let file, diagnostics = parse "fn f() requires + ensures true {\n  x\n}" in
      if codes diagnostics <> [ "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      match file.definitions with
      | [ { value; _ } ] ->
          if Syntax_print.definition value <> "(fn f () error (ensures true) (block x))" then
            fail "got %s" (Syntax_print.definition value)
      | _ -> fail "wrong definitions");
  test "an error in a member leaves the next member parsed" (fun () ->
      let file, diagnostics = parse "trait T {\n  fn a(\n  fn b()\n}" in
      ignore file;
      if List.length diagnostics > 2 then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "nothing is reported before a closer the lexer inserted" (fun () ->
      let _, diagnostics = parse "fn f() {\n  let x = (1 +\n}" in
      if codes diagnostics <> [ "lexer.unclosed_bracket" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a reserved word is reported as reserved" (fun () ->
      error "fn f[T]() where T: Hash {}" ~code:Reserved_word ~at:"where")

(* Syntax from other languages *)

let () =
  test "i++" (fun () -> body_error "count++" ~code:Increment ~at:"++" ~fixed:"count += 1");
  test "i--" (fun () -> body_error "items[0]--" ~code:Increment ~at:"--" ~fixed:"items[0] -= 1");
  test "--x" (fun () ->
      body_error "let y = --x" ~code:Double_negation ~at:"--" ~fixed:"let y = -(-x)");
  test "a comma after a match arm" (fun () ->
      body_error "match a {\n  A => 1,\n  B => 2\n}" ~code:Match_arm_comma ~at:","
        ~fixed:"match a {\n  A => 1\n  B => 2\n}");
  test "x ? a : b" (fun () ->
      body_error "let y = ready ? first : second" ~code:Conditional_operator ~at:"?"
        ~fixed:"let y = if ready { first } else { second }");
  test "x ? a : b takes the whole left side as the condition" (fun () ->
      body_error "let larger = a > b ? a : b" ~code:Conditional_operator ~at:"?"
        ~fixed:"let larger = if a > b { a } else { b }");
  test "let mut" (fun () ->
      body_error "let mut count = 0" ~code:Let_mut ~at:"mut" ~fixed:"var count = 0");
  test "&x" (fun () -> body_error "f(&x)" ~code:Address_of ~at:"&" ~fixed:"f(x)");
  test "& between two names" (fun () ->
      body_error "match& value {\n  _ => todo\n}" ~code:Address_of ~at:"&"
        ~fixed:"match value {\n  _ => todo\n}");
  test "&mut x" (fun () ->
      body_error "sort(&mut items)" ~code:Address_of ~at:"&" ~fixed:"sort(mut items)");
  test "|x| x + 1" (fun () ->
      body_error "let f = items.map(|item| item + 1)" ~code:Closure_bars ~at:"|"
        ~fixed:"let f = items.map(fn(item) { item + 1 })");
  test "|x| with a block" (fun () ->
      body_error "let f = items.map(|item| { item })" ~code:Closure_bars ~at:"|"
        ~fixed:"let f = items.map(fn(item) { item })");
  test "|x| before let ... else" (fun () ->
      body_error "let Some(f) = || g() else {\n  return\n}" ~code:Closure_bars ~at:"||"
        ~fixed:"let Some(f) = (fn() { g() }) else {\n  return\n}");
  test "|| x" (fun () ->
      body_error "let f = run(|| 1)" ~code:Closure_bars ~at:"||" ~fixed:"let f = run(fn() { 1 })");
  test "Point { x: 1.0 }" (fun () ->
      body_error "let p = Point { x: 1.0, y: 2.0 }" ~code:Brace_record ~at:"{ x"
        ~fixed:"let p = Point(x: 1.0, y: 2.0)");
  test "parse::<Int64>(text)" (fun () ->
      body_error "let n = parse::<Int64>(text)" ~code:Turbofish ~at:"<"
        ~fixed:"let n = parse[Int64](text)");
  test "items.map { it.name }" (fun () ->
      body_error "let names = items.map { it.name }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let names = items.map(fn(item) { item.name })");
  test "it in an interpolation is renamed too" (fun () ->
      body_error "let x = items.map { \"${it.name}\" }" ~code:Trailing_lambda ~at:"{ \""
        ~fixed:"let x = items.map(fn(item) { \"${item.name}\" })");
  test "the lambda's parameter is a plain singular, or element" (fun () ->
      body_error "let x = entries.map { it.key }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let x = entries.map(fn(entry) { entry.key })";
      body_error "let x = statuses.map { it.code }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let x = statuses.map(fn(element) { element.code })");
  test "items.map { it.name } is parsed as the call its fix writes" (fun () ->
      let statements, _ = body_of "let names = items.map { it.name }" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let names (call (. items map) (fn (item) (block (. item name)))))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "parse::<List[Int64]> is parsed as the brackets it means" (fun () ->
      let statements, _ = body_of "let n = parse::<List[Int64]>(text)" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let n (call ([] parse ([] List Int64)) text))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "x as Int64" (fun () ->
      body_error "let n = size as Int64" ~code:As_conversion ~at:"as"
        ~fixed:"let n = Int64.from(size)"
        ~alternatives:[ "let n = Int64.try_from(size)" ]);
  test "loop" (fun () ->
      body_error "loop {\n  todo\n}" ~code:Reserved_word ~at:"loop" ~fixed:"while true {\n  todo\n}");
  test "const" (fun () ->
      error "const pi: Float64 = 3.14" ~code:Reserved_word ~at:"const"
        ~fixed:"let pi: Float64 = 3.14");
  test "elif" (fun () ->
      body_error "if a {\n  f()\n}\nelif b {\n  g()\n}" ~code:Elif ~at:"elif"
        ~fixed:"if a {\n  f()\n} else if b {\n  g()\n}")

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

let markdown_files =
  Sys.readdir "../.." |> Array.to_list
  |> List.filter (fun name -> Filename.check_suffix name ".md")
  |> List.sort compare

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
      let text = "use a::b\n\nfn f() -> Int64 {\n  1\n}\n" in
      let tokens, _ = Lexer.lex (source text) in
      if not (Reference.accepts Reference.file (Array.to_list tokens)) then fail "rejected");
  test "GRAMMAR.md's grammar rejects what the parser rejects" (fun () ->
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

let () =
  if !failures > 0 then begin
    Printf.printf "%d failures in %d tests\n" !failures !count;
    exit 1
  end
  else Printf.printf "%d tests pass\n" !count

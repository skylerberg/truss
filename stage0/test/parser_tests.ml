(* The parser's tests of each piece of the grammar. Each test gives an input
   and states exactly what the parser must do with it: the tree, printed
   compactly, or the one diagnostic with its code, position, and fixes. *)

open Harness
open Parse_support

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
  test "a definition records where the parser recovered" (fun () ->
      let recovered text =
        match (fst (parse text)).definitions with
        | [ item ] ->
            List.map
              (fun (span : Syntax.span) -> String.sub item.text span.start (span.stop - span.start))
              item.value.recovered
        | _ -> [ "wrong definitions" ]
      in
      if recovered "fn f() {\n  x as Int64\n}" <> [ "as" ] then fail "the habit is not recorded";
      if recovered "fn f() {\n  let x = (1 +\n}" = [] then
        fail "the inserted closer is not recorded";
      if recovered "fn f() {\n  assert true\n}" <> [] then
        fail "a rule checked after parsing is recorded";
      if recovered "fn f(x: Int64) -> Int64" = [] then fail "the missing body is not recorded");
  test "a missing body's recovery is where the body starts" (fun () ->
      match (fst (parse "fn f(x: Int64) -> Int64\nfn g() {}")).definitions with
      | { value = { kind = Function { body; _ }; recovered; _ }; _ } :: _ ->
          if
            List.map (fun (span : Syntax.span) -> (span.start, span.stop)) recovered
            <> [ (body.span.start, body.span.start) ]
          then fail "recovered at the wrong place"
      | _ -> fail "the signature was not kept");
  test "a recovery at the end of a body lies in the body" (fun () ->
      match (fst (parse "fn f() {\n  let x = (1 +\nfn g() {}\n")).definitions with
      | { value = { kind = Function { body; _ }; recovered; _ }; _ } :: _ ->
          if
            not
              (List.exists
                 (fun (span : Syntax.span) ->
                   span.start < span.stop && body.span.start <= span.start
                   && span.start < body.span.stop)
                 recovered)
          then fail "no recovery inside the body"
      | _ -> fail "wrong definitions");
  test "a failed clause at the end lies in the signature" (fun () ->
      match (fst (parse "fn f() requires")).definitions with
      | { value = { kind = Function { body; _ }; recovered; _ }; _ } :: _ ->
          if not (List.exists (fun (span : Syntax.span) -> span.start < body.span.start) recovered)
          then fail "no recovery in the signature"
      | _ -> fail "wrong definitions");
  test "a definition whose header did not parse keeps its keyword and name" (fun () ->
      let file, _ = parse "fn List[Element].sort[](mut self) {}\ntype Point = 1\nfn f() {}" in
      let printed = Syntax_print.definitions file.definitions in
      if printed <> [ "(error fn List[Element].sort)"; "(error type Point)"; "(fn f () (block))" ]
      then fail "got [%s]" (String.concat "; " printed));
  test "a function without a body keeps its signature" (fun () ->
      let file, _ = parse "fn f(x: Int64) -> Int64\nfn g() {}" in
      match file.definitions with
      | first :: _ ->
          if Syntax_print.definition first.value <> "(fn f ((x: Int64)) -> Int64 (block error))"
          then fail "got %s" (Syntax_print.definition first.value)
      | [] -> fail "no definitions");
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
  test "nested loop bodies count toward the limit" (fun () ->
      let text =
        "fn f() {\n"
        ^ String.concat "" (List.init 300 (fun _ -> "while x {\n"))
        ^ String.concat "" (List.init 300 (fun _ -> "}\n"))
        ^ "}"
      in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "nested blocks without expressions count toward the limit" (fun () ->
      let text =
        "fn f() {\n"
        ^ String.concat "" (List.init 300 (fun _ -> "parallel {\n"))
        ^ String.concat "" (List.init 300 (fun _ -> "}\n"))
        ^ "}"
      in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  let chain ~first ~link ~last =
    first ^ String.concat "" (List.init 10_001 (fun _ -> link)) ^ last
  in
  test "a chain of binary operators longer than the limit is one error" (fun () ->
      let text = chain ~first:"fn f() {\n  let x = 1" ~link:" + 1" ~last:"\n}" in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "a chain of postfix operations longer than the limit is one error" (fun () ->
      let text = chain ~first:"fn f() {\n  let x = a" ~link:".b" ~last:"\n}" in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "a chain of else if branches longer than the limit is one error" (fun () ->
      let text = chain ~first:"fn f() {\n  if a {}" ~link:" else if a {}" ~last:"\n}" in
      if deep text <> [ "parser.nesting_too_deep" ] then fail "no nesting error");
  test "a chain longer than the nesting limit is not nested" (fun () ->
      let text =
        "fn f() {\n  let x = 1" ^ String.concat "" (List.init 300 (fun _ -> " + a.b")) ^ "\n}"
      in
      if codes (snd (parse text)) <> [] then fail "a diagnostic");
  test "an inserted closer in an inner statement leaves errors in the outer one reported" (fun () ->
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
  test "a method is a definition of its own, inside its impl" (fun () ->
      let text = "impl Clock for Fixed {\n  fn now(self) -> Instant {\n    todo\n  }\n}" in
      let file, _ = parse text in
      match file.definitions with
      | [ around; method_ ] ->
          if around.container <> None then fail "the impl is inside something";
          if method_.container <> Some 0 then fail "the method is not inside the impl";
          if method_.text <> "fn now(self) -> Instant {\n    todo\n  }" then
            fail "the method's text is %S" method_.text;
          if method_.base <> 25 then fail "the method starts at %d" method_.base
      | definitions -> fail "%d definitions" (List.length definitions));
  test "a method's tree does not depend on what is around it" (fun () ->
      let method_of text =
        match (fst (parse text)).definitions with
        | [ _; method_ ] -> method_.value
        | _ -> failwith "expected an impl and its method"
      in
      let method_text = "  fn now(self) -> Instant {\n    todo\n  }\n" in
      if
        method_of ("impl Clock for Fixed {\n" ^ method_text ^ "}")
        <> method_of
             ("impl Clock for Other[Element] uses Random {\n  type Tick = Int64\n\n" ^ method_text
            ^ "}")
      then fail "the trees differ");
  test "a definition's diagnostics are placed in the file by its base" (fun () ->
      match pieces "fn g() {}\nfn f() { x = }" with
      | source, tokens, [ _; second ] -> (
          let parsed, _ = Parser.definition source tokens second in
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
        let parsed, _ = Parser.definition source tokens last in
        (parsed.value.value, parsed.diagnostics)
      in
      if parsed text <> parsed ("fn g() {}\n\n\n" ^ text) then fail "the results differ")

(* Node ids *)

(* The ids of a definition's expressions and statements, after checking that
   each child's id comes before its parent's, since a node gets its id when
   it is built, after its children. *)
let ids_of (definition : Syntax.definition) =
  let ids = ref [] in
  let rec expression ~parent (value : Syntax.expression) =
    if value.id >= parent then
      fail "an expression's id %d is not before its parent's %d" value.id parent;
    ids := value.id :: !ids;
    Syntax_walk.expression_parts ~expression:(expression ~parent:value.id)
      ~statement:(statement ~parent:value.id) value
  and statement ~parent (written : Syntax.statement) =
    if written.id >= parent then
      fail "a statement's id %d is not before its parent's %d" written.id parent;
    ids := written.id :: !ids;
    Syntax_walk.statement_parts ~expression:(expression ~parent:written.id)
      ~statement:(statement ~parent:written.id) written
  in
  Syntax_walk.definition (expression ~parent:definition.id) definition;
  !ids

let () =
  test "ids are unique within a definition, children first" (fun () ->
      match
        (fst
           (parse
              "fn f(items: List[Int64]) -> Int64 {\n\
              \  let x = items[0] + \"${items.length()}\"\n\
              \  if x > 0 { x } else { 0 }\n\
               }"))
          .definitions
      with
      | [ { value; _ } ] ->
          let ids = ids_of value in
          if List.length (List.sort_uniq compare ids) <> List.length ids then fail "ids repeat";
          if ids = [] then fail "no ids"
      | _ -> fail "wrong definitions");
  test "a definition whose header was read again has an id of its own" (fun () ->
      match (fst (parse "fn List[Element].sort[](mut self) {}")).definitions with
      | [
       {
         value = { kind = Definition_error { name = Some (Member_name (head, name)); _ }; id; _ };
         _;
       };
      ] ->
          if List.length (List.sort_uniq compare [ id; head.id; name.id ]) <> 3 then
            fail "ids repeat"
      | _ -> fail "wrong definitions")

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
  test "a function type's requires names its inputs" (fun () ->
      definition "fn f(visit: (fn(index: USize) requires index < 3)) {}"
        "(fn f ((visit: (fn (index: USize) (requires (< index 3))))) (block))");
  test "requires in a function type needs every input named" (fun () ->
      error "fn f(value: (fn(Item) requires true)) {}" ~code:Function_type_names ~at:"fn(Item)");
  test "a function type without requires names no input" (fun () ->
      error "fn f(value: fn(item: Item)) {}" ~code:Function_type_names ~at:"fn(item");
  test "ensures in a function type" (fun () ->
      error "fn f(value: (fn(item: Item) ensures true)) {}" ~code:Unexpected_token ~at:"ensures");
  test "requires on a function type that is not a parameter's" (fun () ->
      error "type T(visit: (fn(index: USize) requires index < 3))" ~code:Misplaced_requires
        ~at:"requires";
      error "fn f(visits: List[(fn(index: USize) requires index < 3)]) {}" ~code:Misplaced_requires
        ~at:"requires");
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
  test "no missing token is reported at the end of an interpolation that a line break ended"
    (fun () ->
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
        "(parallel-for player (mut players) (block))";
      statement "concurrent for connection in listener.connections() {}"
        "(concurrent-for connection (call (. listener connections)) (block))");
  test "a loop has at most one decreases" (fun () ->
      body_error "while a\n  decreases b\n  decreases c\n{}" ~code:Repeated_clause ~at:"decreases c");
  test "parallel, concurrent, proof, and yield" (fun () ->
      statement "parallel {\n  let a = 1\n  let b = 2\n}" "(parallel (block (let a 1) (let b 2)))";
      statement "concurrent {\n  let a = f()\n  g()\n}"
        "(concurrent (block (let a (call f)) (call g)))";
      statement "proof {\n  lemma()\n}" "(proof (block (call lemma)))");
  test "a match arm's body is a statement" (fun () ->
      statement "match event {\n  Click => clicks += 1\n  Done =>\n    finish()\n}"
        "(match (event) (=> Click (+= clicks 1)) (=> Done (call finish)))")

let () = finish ()

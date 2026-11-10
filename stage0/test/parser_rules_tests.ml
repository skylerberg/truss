(* The parser's tests of whole definitions, precedence and the combinations
   that need parentheses, the checks on a whole definition, recovery, and
   the habits of other languages it recognizes. *)

open Harness
open Parse_support

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
  test "a quantifier over a range is an expression in code" (fun () ->
      statement "let x = forall i in s => i" "(let x (forall (in i s) i))");
  test "a quantifier over a type in a test" (fun () ->
      error "test \"a\" {\n  let x = forall value: Int64 => value == value\n}"
        ~code:Specification_only ~at:"forall");
  test "==> in a test" (fun () ->
      error "test \"a\" {\n  let x = a ==> b\n}" ~code:Specification_only ~at:"==>");
  test "==> in a constant" (fun () ->
      error "let x: Bool = a ==> b" ~code:Specification_only ~at:"==>");
  test "==> and a quantifier over a type in a function's body are left to the type checker"
    (fun () ->
      definition "fn f() -> Bool {\n  a ==> forall value: Int64 => value == value\n}"
        "(fn f () -> Bool (block (==> a (forall value: Int64 (== value value)))))");
  test "a yielding method's parameter cannot be named yielded or finished" (fun () ->
      error "fn T.each(self, yielded: Int64) yields Int64 {\n  yield 1\n}" ~code:Reserved_name
        ~at:"yielded";
      definition "fn f(finished: Bool) {}" "(fn f ((finished: Bool)) (block))");
  test "a loop's cost clause" (fun () ->
      statement "for row in rows\n  cost time O(yielded.length())\n{}"
        "(for row rows (cost time (O (call (. yielded length)))) (block))");
  test "a loop's cost is not amortized or finite" (fun () ->
      body_error "while a\n  cost amortized time O(1)\n{}" ~code:Loop_cost_bound ~at:"cost";
      body_error "while a\n  cost time finite\n{}" ~code:Loop_cost_bound ~at:"cost");
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

let () = finish ()

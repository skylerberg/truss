let () =
  Harness.test "a method, its receiver, and its result" (fun () ->
      Parse_support.expect_definition
        "fn List[Element: Ordered].least(mut self, by: Order = Order.Ascending) lends mut Element \
         {}"
        "(fn List[Element: Ordered].least (mut self (by: Order (= (. Order Ascending)))) lends mut \
         Element (block))";
      Parse_support.expect_definition "fn hourly.Forecast.summary(self) -> String { todo }"
        "(fn hourly.Forecast.summary (self) -> String (block todo))");
  Harness.test "clauses in the order written" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.clauses_in_the_order_written
        "(fn f ((x: Int64)) -> Int64 (ensures (> result x)) (requires (> x 0)) (decreases x 1) \
         (uses Clock) (block x))");
  Harness.test "cost clauses" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.cost_clauses
        "(fn f ((visit: (fn (Item) (cost time (O 1))))) (cost amortized time (O (* (call (. items \
         length)) (call time visit)))) (cost allocations (<= 1)) (cost (calls visit) (== 2)) (cost \
         (calls FileRead.read) (== 3)) (cost (calls FileRead) (== 4)) (block))");
  Harness.test "parsing continues after a misspelled cost word" (fun () ->
      Parse_support.expect_error "fn f() cost tme O(1) {}" ~code:Cost_word ~at:"tme"
        ~fixed:("tme", "time");
      let _, diagnostics = Parse_support.parse "fn f() cost tme fnite {}" in
      if Support.list_codes diagnostics <> [ "parser.cost_word"; "parser.cost_word" ] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a trait's body on the next line" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.trait_with_its_body_on_the_next_line
        "(trait T (type K))");
  Harness.test "a misspelled cost word has a fix" (fun () ->
      Parse_support.expect_error "fn f() cost allocation == 0 {}" ~code:Cost_word ~at:"allocation"
        ~fixed:("allocation", "allocations"));
  Harness.test "cost potential belongs to a type" (fun () ->
      Parse_support.expect_error "fn f() cost potential x {}" ~code:Misplaced_potential
        ~at:"potential");
  Harness.test "uses appears at most once" (fun () ->
      Parse_support.expect_error "fn f() uses Clock uses Random {}" ~code:Repeated_clause
        ~at:"uses Random");
  Harness.test "modifies lists the parts that a function changes, at most once, with no condition"
    (fun () ->
      Parse_support.expect_definition "fn f(a: mut A)\n  modifies a.b, a.c.d\n{}"
        "(fn f ((a: mut A)) (modifies (. a b) (. (. a c) d)) (block))";
      Parse_support.expect_error "fn f(a: mut A) modifies a.b modifies a.c {}" ~code:Repeated_clause
        ~at:"modifies a.c";
      Parse_support.expect_error "fn f(a: mut A) modifies a.b when A: Display {}"
        ~code:Unexpected_token ~at:"when";
      Parse_support.expect_error "fn f(visit: (fn(mut A) modifies a.b)) {}" ~code:Unexpected_token
        ~at:"modifies");
  Harness.test "a missing body gets { todo }" (fun () ->
      Parse_support.expect_error "fn f() -> Int64\nfn g() {}" ~code:Missing_body ~at:"\nfn g"
        ~fixed:("Int64", "Int64 { todo }"));
  Harness.test "self only in a method" (fun () ->
      Parse_support.expect_error "fn f(self) {}" ~code:Misplaced_self ~at:"self");
  Harness.test "self only first" (fun () ->
      Parse_support.expect_error "fn T.f(x: Int64, self) {}" ~code:Misplaced_self ~at:"self");
  Harness.test "a parameter cannot be named result" (fun () ->
      Parse_support.expect_error "fn f(result: Int64) {}" ~code:Reserved_specification_name
        ~at:"result");
  Harness.test "a function cannot be named old" (fun () ->
      Parse_support.expect_error "fn old() {}" ~code:Reserved_specification_name ~at:"old");
  Harness.test "types" (fun () ->
      Parse_support.expect_definition "type Point(x: Float64, y: Float64 = 0.0)"
        "(type Point ((x: Float64) (y: Float64 (= 0e0))))";
      Parse_support.expect_definition "type DiscardLog()" "(type DiscardLog ())";
      Parse_support.expect_definition "type Bit = Zero | One" "(type Bit (= Zero One))";
      Parse_support.expect_definition "public opaque type Session = todo"
        "(public opaque (type Session = todo))";
      Parse_support.expect_definition Fixtures.Parser_rules.types
        "(type Tree[Value] (= Leaf (indirect Node ((left: Tree[Value]) (right: Tree[Value])))) \
         (invariant (call is_balanced self)) (derives Equal Hash) (cost potential (call size \
         self)))");
  Harness.test "a trait" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.trait
        "(trait Ordered : Equal (type Key: Hash) (law transitive ((a: Self) (b: Self)) (requires \
         (<= a b)) (block true)) (fn compare (self (other: Self)) -> Ordering) (fn max (own self \
         (other: own Self)) -> Self (ensures true) (block self)))";
      Parse_support.expect_definition "trait Loggable: Display + Hash {}"
        "(trait Loggable : Display + Hash)");
  Harness.test "an impl" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.impl
        "(impl FileRead for FilesWithin (uses FileRead) (type Error = FileError) (fn read (self) \
         -> Bytes (block todo)))";
      Parse_support.expect_definition "impl Display for List[Element: Display] {}"
        "(impl Display for List[Element: Display])");
  Harness.test "an associated capability set" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.associated_capability_set
        "(trait Feed (capability Uses) (fn pull (mut self) -> Int64 (uses Self.Uses)))";
      Parse_support.expect_definition Fixtures.Parser_rules.associated_capability_set_in_an_impl
        "(impl Feed for Zip[First: Feed, Second: Feed] (capability Uses = First.Uses Second.Uses \
         Clock))";
      Parse_support.expect_definition Fixtures.Parser_rules.associated_capability_set_in_uses
        "(fn drain[Source: Feed] ((source: mut Source)) (uses Source.Uses Clock) (block))";
      Parse_support.expect_definition "fn run(step: (fn() uses Self.Uses)) {}"
        "(fn run ((step: (fn () (uses Self.Uses)))) (block))");
  Harness.test "an associated capability set is named after a dot" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.uses_self ~code:Unexpected_token ~at:"\n{";
      Parse_support.expect_error
        Fixtures.Parser_rules.impl_declaring_a_capability_set_without_a_value ~code:Unexpected_token
        ~at:"}";
      Parse_support.expect_error "type Point(x: Int64)\n  derives Self.Uses" ~code:Unexpected_token
        ~at:"Self");
  Harness.test "a capability" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.capability
        "(capability Clock (fn now () -> Instant) (fn sleep ((duration: Duration))))");
  Harness.test "a capability's methods take no self" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.capability_method_taking_self
        ~code:Misplaced_self ~at:"self");
  Harness.test "an impl's methods need bodies" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.impl_method_without_a_body ~code:Missing_body
        ~at:"\n}" ~fixed:("Instant", "Instant { todo }"));
  Harness.test "constants" (fun () ->
      Parse_support.expect_definition "public let UInt8.maximum: UInt8 = 255"
        "(public (let UInt8.maximum : UInt8 255))";
      Parse_support.expect_definition "let pi: Float64 = 3.14" "(let pi : Float64 314e-2)");
  Harness.test "a test, a theorem, and a law's proof" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.test_using_file_write
        "(test \"writes\" (uses FileWrite) (block (assert true)))";
      Parse_support.expect_definition Fixtures.Parser_rules.public_theorem
        "(public (theorem keeps[Element] ((items: List[Element])) (ensures true) (block)))";
      Parse_support.expect_definition "proof Monoid.associative for Int64 {\n  lemma()\n}"
        "(proof Monoid.associative for Int64 (block (call lemma)))");
  Harness.test "a law's proof names its type as an impl does, with generic parameters" (fun () ->
      Parse_support.expect_definition
        "proof Ordered.transitive for Box[Item: Ordered] {\n  lemma()\n}"
        "(proof Ordered.transitive for Box[Item: Ordered] (block (call lemma)))");
  Harness.test "a test's name is a plain string" (fun () ->
      Parse_support.expect_error "test \"a${b}\" {}" ~code:Interpolation_not_allowed ~at:"\"a");
  Harness.test "an impl takes no visibility" (fun () ->
      Parse_support.expect_error "public impl A for B {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:("public impl", "impl"));
  Harness.test
    "an impl's trait arguments declare no generic parameter, as the recursive type check assumes"
    (fun () ->
      Parse_support.expect_error "impl Selected[Carried: Shown] for Marker {}"
        ~code:Unexpected_token ~at:":");
  Harness.test "an impl's trait arguments hold no function type, at any depth" (fun () ->
      Parse_support.expect_error "impl From[fn(Int64) -> Int64] for Handler {}"
        ~code:Misplaced_function_type ~at:"fn(";
      Parse_support.expect_error "impl From[List[fn() -> Int64]] for Handler {}"
        ~code:Misplaced_function_type ~at:"fn(");
  Harness.test "an impl's trait arguments hold no associated type, so the impl overlaps no other"
    (fun () ->
      Parse_support.expect_error
        "impl Multiply[Dimension.Scalar] for Quantity[Dimension: Measure] {}"
        ~code:Misplaced_associated_type ~at:"Dimension.Scalar";
      Parse_support.expect_error "impl Add[Self.Output] for Meters {}"
        ~code:Misplaced_associated_type ~at:"Self.Output");
  Harness.test "a law's proof holds no trait argument that an impl cannot hold" (fun () ->
      Parse_support.expect_error "proof From[fn() -> Int64].round_trips for Handler {}"
        ~code:Misplaced_function_type ~at:"fn(";
      Parse_support.expect_error "proof Add[Self.Output].associative for Meters {}"
        ~code:Misplaced_associated_type ~at:"Self.Output");
  Harness.test "an impl's trait takes no constraint, which its body would override" (fun () ->
      Parse_support.expect_error "impl Cursor[Element = Int64] for Numbers {}"
        ~code:Misplaced_constraint ~at:"Element = Int64";
      Parse_support.expect_error "impl Convert[Int64, Output = Text] for Number {}"
        ~code:Misplaced_constraint ~at:"Output = Text";
      Parse_support.expect_error "proof Cursor[Element = Int64].ordered for Numbers {}"
        ~code:Misplaced_constraint ~at:"Element = Int64");
  Harness.test "an impl's trait arguments may be types, its generic parameters, Self, and counts"
    (fun () ->
      Parse_support.expect_definition "impl Add[Element] for Vector[Element] {}"
        "(impl Add[Element] for Vector[Element])";
      Parse_support.expect_definition
        "impl From[List[map.Entry[Key, Value]]] for Table[Key, Value] {}"
        "(impl From[List[map.Entry[Key, Value]]] for Table[Key, Value])";
      Parse_support.expect_definition "impl Add[Self] for Meters {}" "(impl Add[Self] for Meters)";
      Parse_support.expect_definition "impl From[Array[UInt8, 32]] for Digest {}"
        "(impl From[Array[UInt8, 32]] for Digest)");
  Harness.test "a test takes no visibility" (fun () ->
      Parse_support.expect_error "internal test \"a\" {}" ~code:Misplaced_visibility ~at:"internal"
        ~fixed:("internal test", "test"));
  Harness.test "a law's proof takes no visibility" (fun () ->
      Parse_support.expect_error "public proof A.b for C {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:("public proof", "proof"));
  Harness.test "a tuple type" (fun () ->
      Parse_support.expect_definition "tuple type Span(start: UInt64, end: UInt64)"
        "(tuple type Span ((start: UInt64) (end: UInt64)))";
      Parse_support.expect_definition "public tuple type Span(start: UInt64, end: UInt64)"
        "(public (tuple type Span ((start: UInt64) (end: UInt64))))");
  Harness.test "only a record with two or more fields is a tuple type" (fun () ->
      Parse_support.expect_error "tuple type Id(number: UInt64)" ~code:Misplaced_tuple ~at:"tuple"
        ~fixed:("tuple type", "type");
      Parse_support.expect_error "tuple type Bit = Zero | One" ~code:Misplaced_tuple ~at:"tuple"
        ~fixed:("tuple type", "type"));
  Harness.test "only `tuple` comes before `type`" (fun () ->
      Parse_support.expect_error "tupel type Span(start: UInt64, end: UInt64)" ~code:Misplaced_tuple
        ~at:"tupel" ~fixed:("tupel", "tuple");
      Parse_support.expect_error "record type Span(start: UInt64, end: UInt64)"
        ~code:Misplaced_tuple ~at:"record" ~fixed:("record type", "type"));
  Harness.test "a tuple pattern takes no type annotation" (fun () ->
      Parse_support.expect_body_error "let low, high: Span = span" ~code:Unexpected_token ~at:":");
  Harness.test "only a type is opaque" (fun () ->
      Parse_support.expect_error "public opaque fn f() {}" ~code:Misplaced_opaque ~at:"opaque"
        ~fixed:("opaque fn", "fn"));
  Harness.test "an impl with a visibility and a modifier has one diagnostic" (fun () ->
      Parse_support.expect_error "public opaque impl A for B {}" ~code:Misplaced_visibility
        ~at:"public" ~fixed:("public opaque impl", "impl"))

let () =
  let expect_combination text ~at ~code ~fixes =
    match fixes with
    | fixed :: alternatives ->
        Parse_support.expect_body_error ("let x = " ^ text) ~code ~at ~fixed:(text, fixed)
          ~alternatives:(List.map (fun alternative -> (text, alternative)) alternatives)
    | [] -> Parse_support.expect_body_error ("let x = " ^ text) ~code ~at
  in
  Harness.test "bitwise and comparison: Rust's reading, then C's" (fun () ->
      expect_combination "flags & mask == 0" ~at:"==" ~code:Needs_parentheses
        ~fixes:[ "(flags & mask) == 0"; "flags & (mask == 0)" ]);
  Harness.test "shift and addition: C and Rust's reading, then Go and Swift's" (fun () ->
      expect_combination "a << b + 1" ~at:"<<" ~code:Needs_parentheses
        ~fixes:[ "a << (b + 1)"; "(a << b) + 1" ]);
  Harness.test "a reading whose parentheses would mix operators inside them is not offered"
    (fun () ->
      expect_combination "a + b * c << d" ~at:"<<" ~code:Needs_parentheses
        ~fixes:[ "(a + b * c) << d" ]);
  Harness.test "& and | read the same everywhere" (fun () ->
      expect_combination "a & b | c" ~at:"|" ~code:Needs_parentheses ~fixes:[ "(a & b) | c" ]);
  Harness.test "& and | read the same on the right" (fun () ->
      expect_combination "c | a & b" ~at:"|" ~code:Needs_parentheses ~fixes:[ "c | (a & b)" ]);
  Harness.test "a reading that needs more parentheses inside && gets them" (fun () ->
      expect_combination "a & b == c && d" ~at:"==" ~code:Needs_parentheses
        ~fixes:[ "(a & b) == c && d"; "(a & (b == c)) && d" ]);
  Harness.test "the other reading takes the operand next to the operator" (fun () ->
      expect_combination "s & a + b + c" ~at:"&" ~code:Needs_parentheses
        ~fixes:[ "s & (a + b + c)"; "(s & a) + b + c" ]);
  Harness.test "the same bitwise operator chains" (fun () ->
      Parse_support.expect_statement "let x = a | b | c" "(let x (| (| a b) c))");
  Harness.test "shifts chain" (fun () ->
      Parse_support.expect_statement "let x = a << 1 >> 2" "(let x (>> (<< a 1) 2))");
  Harness.test "&& and || cannot be mixed" (fun () ->
      expect_combination "a && b || c" ~at:"||" ~code:Needs_parentheses
        ~fixes:[ "(a && b) || c"; "a && (b || c)" ]);
  Harness.test "comparisons do not chain" (fun () ->
      expect_combination "a < b < c" ~at:"< c" ~code:Needs_parentheses ~fixes:[ "a < b && b < c" ]);
  Harness.test "comparisons joined under || get parentheses" (fun () ->
      expect_combination "a || b <= c < d" ~at:"< d" ~code:Needs_parentheses
        ~fixes:[ "a || (b <= c && c < d)" ]);
  Harness.test "a chained comparison without a simple middle has no fix" (fun () ->
      expect_combination "a < f(b) < c" ~at:"< c" ~code:Needs_parentheses ~fixes:[]);
  Harness.test "is does not chain" (fun () ->
      expect_combination "a is B == c" ~at:"==" ~code:Needs_parentheses ~fixes:[]);
  Harness.test "is beside & has no fix that puts & inside the pattern" (fun () ->
      expect_combination "value is Ready & mask" ~at:"&" ~code:Needs_parentheses
        ~fixes:[ "(value is Ready) & mask" ]);
  Harness.test "ranges do not chain" (fun () ->
      expect_combination "0..10..20" ~at:"..20" ~code:Needs_parentheses ~fixes:[]);
  Harness.test "==> does not chain: Dafny's reading first" (fun () ->
      Parse_support.expect_error "fn f() requires a ==> b ==> c {}" ~code:Needs_parentheses
        ~at:"==> c"
        ~fixed:("fn f() requires a ==> b ==> c {}", "fn f() requires a ==> (b ==> c) {}")
        ~alternatives:[ ("fn f() requires a ==> b ==> c {}", "fn f() requires (a ==> b) ==> c {}") ]);
  Harness.test "parentheses settle a combination" (fun () ->
      Parse_support.expect_statement "let x = (flags & mask) == 0"
        "(let x (== (paren (& flags mask)) 0))");
  Harness.test "a quantifier may end && in a specification" (fun () ->
      Parse_support.expect_definition "fn f() requires a && exists x in s => x {}"
        "(fn f () (requires (&& a (exists (in x s) x))) (block))");
  Harness.test "a quantifier elsewhere needs parentheses" (fun () ->
      Parse_support.expect_error "fn f() requires count + forall x in s => x {}"
        ~code:Needs_parentheses ~at:"forall"
        ~fixed:("forall x in s => x", "(forall x in s => x)"));
  Harness.test "echo as an operand needs parentheses" (fun () ->
      Parse_support.expect_body_error "let x = count + echo x" ~code:Needs_parentheses ~at:"echo"
        ~fixed:("echo x", "(echo x)"));
  Harness.test "a fix's title spells the fixed expression only when it is short" (fun () ->
      let list_titles text =
        List.concat_map
          (fun (diagnostic : Diagnostic.t) ->
            List.map (fun (fix : Source.span Diagnostic.fix) -> fix.title) diagnostic.fixes)
          (snd (Parse_support.parse_body text))
      in
      Harness.expect_strings ~expected:[ "Write `a < b && b < c`" ]
        (list_titles "let x = a < b < c");
      Harness.expect_strings
        ~expected:[ "Join the comparisons with `&&`" ]
        (list_titles
           "let x = first_operand_with_a_long_name < second_operand_with_a_long_name < \
            third_operand_with_a_long_name"));
  Harness.test "each combination in a chain is reported" (fun () ->
      let _, diagnostics = Parse_support.parse_body "let x = a < b < c < d" in
      if List.length diagnostics <> 2 then
        Harness.fail "got %d diagnostics" (List.length diagnostics))

let () =
  Harness.test "a quantifier over a range is an expression in code" (fun () ->
      Parse_support.expect_statement "let x = forall i in s => i" "(let x (forall (in i s) i))");
  Harness.test "a lending method's parameter cannot be named final" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.lending_method_with_a_parameter_named_final
        ~code:Reserved_specification_name ~at:"final";
      Parse_support.expect_definition "fn f(final: Bool) {}" "(fn f ((final: Bool)) (block))");
  Harness.test "a loop's cost clause" (fun () ->
      Parse_support.expect_statement "for row in rows\n  cost time O(visited.length())\n{}"
        "(for row rows (cost time (O (call (. visited length)))) (block))");
  Harness.test "a loop's cost is not amortized" (fun () ->
      Parse_support.expect_body_error "while a\n  cost amortized time O(1)\n{}"
        ~code:Loop_cost_bound ~at:"cost");
  Harness.test "an amortized bound is an O bound on a metric" (fun () ->
      Parse_support.expect_error "fn f()\n  cost amortized allocations <= 0\n{}"
        ~code:Amortized_bound ~at:"amortized";
      Parse_support.expect_error "fn f(visit: fn())\n  cost amortized calls(visit) O(1)\n{}"
        ~code:Amortized_bound ~at:"amortized";
      Parse_support.expect_error "fn f(visit: (fn() cost amortized allocations == 0)) {}"
        ~code:Amortized_bound ~at:"amortized");
  Harness.test "specifications allow forall" (fun () ->
      Parse_support.expect_definition
        "type S(items: List[Int64])\n  invariant forall i in items => i > 0"
        "(type S ((items: List[Int64])) (invariant (forall (in i items) (> i 0))))";
      Parse_support.expect_statement "while a\n  invariant forall i in s => i\n{}"
        "(while a (invariant (forall (in i s) i)) (block))");
  Harness.test "assert outside tests and proofs" (fun () ->
      Parse_support.expect_body_error "assert true" ~code:Misplaced_assert ~at:"assert");
  Harness.test "assert in a proof block" (fun () ->
      Parse_support.expect_statement "proof {\n  assert true\n}" "(proof (block (assert true)))");
  Harness.test "assert by evaluation and by bit_vector name how the assertion is proven" (fun () ->
      Parse_support.expect_statement "proof {\n  assert ready by evaluation\n}"
        "(proof (block (assert ready by evaluation)))";
      Parse_support.expect_statement "proof {\n  assert ready by bit_vector\n}"
        "(proof (block (assert ready by bit_vector)))");
  Harness.test "assert in a lambda in a test" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.assert_in_a_lambda_in_a_test
        ~code:Misplaced_assert ~at:"assert");
  Harness.test "a proof block outside a function's body" (fun () ->
      Parse_support.expect_error Fixtures.Parser_rules.proof_block_in_a_test ~code:Misplaced_proof
        ~at:"proof");
  Harness.test "a method that lends" (fun () ->
      Parse_support.expect_definition Fixtures.Parser_rules.method_that_lends
        "(fn Grid.cell (mut self (position: Position)) lends mut Cell (block (mut ([] (. self \
         cells) 0))))");
  Harness.test "yield and yields are identifiers" (fun () ->
      Parse_support.expect_definition "fn yields(yield: Int64) -> Int64 { yield }"
        "(fn yields ((yield: Int64)) -> Int64 (block yield))");
  Harness.test "lends own" (fun () ->
      Parse_support.expect_error "fn T.part(own self) lends own Part {}" ~code:Lends_own
        ~at:"own Part" ~fixed:("own Part", "Part"));
  Harness.test "break outside a loop" (fun () ->
      Parse_support.expect_body_error "break" ~code:Misplaced_loop_exit ~at:"break");
  Harness.test "continue across a lambda" (fun () ->
      Parse_support.expect_body_error "for x in s {\n  f(fn() { continue })\n}"
        ~code:Misplaced_loop_exit ~at:"continue");
  Harness.test "break and continue in a loop" (fun () ->
      Parse_support.expect_statement "while true {\n  if a { break } else { continue }\n}"
        "(while true (block (if a (block break) (block continue))))");
  Harness.test "return leaving a parallel block" (fun () ->
      Parse_support.expect_body_error "parallel {\n  return\n}" ~code:Exits_parallel ~at:"return");
  Harness.test "? leaving a parallel for" (fun () ->
      Parse_support.expect_body_error "parallel for x in s {\n  let y = f(x)?\n}"
        ~code:Exits_parallel ~at:"?");
  Harness.test "break in a parallel for" (fun () ->
      Parse_support.expect_body_error "parallel for x in s {\n  break\n}" ~code:Exits_parallel
        ~at:"break");
  Harness.test "continue in a parallel for" (fun () ->
      Parse_support.expect_statement "parallel for x in s {\n  continue\n}"
        "(parallel-for x s (block continue))");
  Harness.test "break leaving a branch" (fun () ->
      Parse_support.expect_body_error "while a {\n  parallel {\n    break\n  }\n}"
        ~code:Exits_parallel ~at:"break");
  Harness.test "a loop inside a branch" (fun () ->
      Parse_support.expect_statement "parallel {\n  for x in s { break }\n}"
        "(parallel (block (for x s (block break))))");
  Harness.test "return in a lambda inside a branch" (fun () ->
      Parse_support.expect_statement "parallel {\n  f(fn() { return })\n}"
        "(parallel (block (call f (fn () (block (return))))))");
  Harness.test "return, ?, and break leaving a concurrent block or loop" (fun () ->
      Parse_support.expect_statement "concurrent {\n  return\n  let y = f(x)?\n}"
        "(concurrent (block (return) (let y (? (call f x)))))";
      Parse_support.expect_statement
        "concurrent for x in s {\n  if a { break } else { continue }\n}"
        "(concurrent-for x s (block (if a (block break) (block continue))))";
      Parse_support.expect_statement "while a {\n  concurrent {\n    break\n  }\n}"
        "(while a (block (concurrent (block break))))");
  Harness.test "return leaving a parallel block inside a concurrent one" (fun () ->
      Parse_support.expect_body_error "concurrent {\n  parallel {\n    return\n  }\n}"
        ~code:Exits_parallel ~at:"return");
  Harness.test "echo in a specification" (fun () ->
      Parse_support.expect_error "fn f(x: Int64) requires echo x > 0 {}" ~code:Echo_in_specification
        ~at:"echo");
  Harness.test "a statement rule applies in every block" (fun () ->
      Parse_support.expect_body_error Fixtures.Parser_rules.assert_in_a_provide_block
        ~code:Misplaced_assert ~at:"assert");
  Harness.test "echo in a proof" (fun () ->
      Parse_support.expect_body_error "proof {\n  echo x\n}" ~code:Echo_in_specification ~at:"echo")

let () =
  Harness.test "an error in a statement leaves the next one parsed" (fun () ->
      Parse_support.expect_recovered_statements ~codes:[ "parser.unexpected_token" ]
        "let x = 1 2 3\nlet y = 2" [ "error"; "(let y 2)" ]);
  Harness.test "each bad item in brackets gets its own error" (fun () ->
      Parse_support.expect_recovered_statements
        ~codes:[ "parser.unexpected_token"; "parser.unexpected_token"; "parser.unexpected_token" ]
        "f(1 +, x, 2 3, g(a b))\nlet y = 2"
        [ "(call f error x error (call g error))"; "(let y 2)" ]);
  Harness.test "an error in a clause leaves the body parsed" (fun () ->
      Parse_support.expect_recovered_definitions ~codes:[ "parser.unexpected_token" ]
        Fixtures.Parser_rules.broken_requires_clause
        [ "(fn f () error (ensures true) (block x))" ]);
  Harness.test "an error in a member leaves the next member parsed" (fun () ->
      let file, diagnostics =
        Parse_support.parse Fixtures.Parser_rules.trait_with_an_unclosed_member
      in
      ignore file;
      if List.length diagnostics > 2 then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "nothing is reported before a closer the lexer inserted" (fun () ->
      let _, diagnostics = Parse_support.parse Fixtures.Parser_rules.unclosed_parenthesis in
      if Support.list_codes diagnostics <> [ "lexer.unclosed_bracket" ] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a reserved word is reported as reserved" (fun () ->
      Parse_support.expect_error "fn f[T]() where T: Hash {}" ~code:Reserved_word ~at:"where")

let () =
  Harness.test "i++" (fun () ->
      Parse_support.expect_body_error "count++" ~code:Increment ~at:"++"
        ~fixed:("count++", "count += 1"));
  Harness.test "i--" (fun () ->
      Parse_support.expect_body_error "items[0]--" ~code:Increment ~at:"--"
        ~fixed:("items[0]--", "items[0] -= 1"));
  Harness.test "--x" (fun () ->
      Parse_support.expect_body_error "let y = --x" ~code:Double_negation ~at:"--"
        ~fixed:("let y = --x", "let y = -(-x)"));
  Harness.test "a fix that would add an error is withheld" (fun () ->
      let list_fixes text code =
        match
          List.find_opt
            (fun (diagnostic : Diagnostic.t) -> diagnostic.code = Parser code)
            (snd (Parse_support.parse ("fn example() {\n" ^ text ^ "\n}")))
        with
        | Some diagnostic -> diagnostic.fixes
        | None -> Harness.fail "no %s for %S" (Diagnostic.Code.name (Parser code)) text
      in
      if list_fixes "count :=== 0" Short_declaration <> [] then Harness.fail "offered the `let` fix");
  Harness.test "a comma between arms on one line becomes a line break" (fun () ->
      List.iter
        (fun (written, expected) ->
          let text = "fn example() {\n" ^ written ^ "\n}" in
          match
            List.find_opt
              (fun (diagnostic : Diagnostic.t) -> diagnostic.code = Parser Match_arm_comma)
              (snd (Parse_support.parse text))
          with
          | Some { fixes = [ fix ]; _ } ->
              let fixed = Diagnostic.apply_edits text fix.edits in
              if fixed <> "fn example() {\n" ^ expected ^ "\n}" then Harness.fail "fixed %S" fixed;
              if snd (Parse_support.parse fixed) <> [] then Harness.fail "%S does not parse" fixed
          | _ -> Harness.fail "no single comma fix for %S" written)
        [
          ("match a { A => 1, B => 2 }", "match a { A => 1\nB => 2 }");
          ("match a {\n  A => 0,B(b) => 1\n}", "match a {\n  A => 0\nB(b) => 1\n}");
        ]);
  Harness.test "a comma after a match arm" (fun () ->
      Parse_support.expect_body_error "match a {\n  A => 1,\n  B => 2\n}" ~code:Match_arm_comma
        ~at:"," ~fixed:("A => 1,", "A => 1"));
  Harness.test "x ? a : b" (fun () ->
      Parse_support.expect_body_error "let y = ready ? first : second" ~code:Conditional_operator
        ~at:"?"
        ~fixed:("ready ? first : second", "if ready { first } else { second }"));
  Harness.test "x ? a : b takes the whole left side as the condition" (fun () ->
      Parse_support.expect_body_error "let larger = a > b ? a : b" ~code:Conditional_operator
        ~at:"?"
        ~fixed:("a > b ? a : b", "if a > b { a } else { b }"));
  Harness.test "let mut" (fun () ->
      Parse_support.expect_body_error "let mut count = 0" ~code:Let_mut ~at:"mut"
        ~fixed:("let mut", "var"));
  Harness.test "&x" (fun () ->
      Parse_support.expect_body_error "f(&x)" ~code:Address_of ~at:"&" ~fixed:("f(&x)", "f(x)"));
  Harness.test "& between two names" (fun () ->
      Parse_support.expect_body_error "match& value {\n  _ => todo\n}" ~code:Address_of ~at:"&"
        ~fixed:("match&", "match"));
  Harness.test "&mut x" (fun () ->
      Parse_support.expect_body_error "sort(&mut items)" ~code:Address_of ~at:"&"
        ~fixed:("&mut", "mut"));
  Harness.test "|x| x + 1" (fun () ->
      Parse_support.expect_body_error "let f = items.map(|item| item + 1)" ~code:Closure_bars
        ~at:"|"
        ~fixed:("|item| item + 1", "fn(item) { item + 1 }"));
  Harness.test "|x| with a block" (fun () ->
      Parse_support.expect_body_error "let f = items.map(|item| { item })" ~code:Closure_bars
        ~at:"|" ~fixed:("|item|", "fn(item)"));
  Harness.test "|x| before let ... else" (fun () ->
      Parse_support.expect_body_error Fixtures.Parser_rules.closure_before_let_else
        ~code:Closure_bars ~at:"||"
        ~fixed:("let Some(f) = || g() else {", "let Some(f) = (fn() { g() }) else {"));
  Harness.test "|| x" (fun () ->
      Parse_support.expect_body_error "let f = run(|| 1)" ~code:Closure_bars ~at:"||"
        ~fixed:("let f = run(|| 1)", "let f = run(fn() { 1 })"));
  Harness.test "Point { x: 1.0 }" (fun () ->
      Parse_support.expect_body_error "let p = Point { x: 1.0, y: 2.0 }" ~code:Brace_record
        ~at:"{ x"
        ~fixed:("Point { x: 1.0, y: 2.0 }", "Point(x: 1.0, y: 2.0)"));
  Harness.test "parse::<Int64>(text)" (fun () ->
      Parse_support.expect_body_error "let n = parse::<Int64>(text)" ~code:Turbofish ~at:"<"
        ~fixed:("parse::<Int64>", "parse[Int64]"));
  Harness.test "List<String> in a type" (fun () ->
      Parse_support.expect_body_error "let names: List<String> = []" ~code:Angle_brackets ~at:"<"
        ~fixed:("List<String>", "List[String]");
      Parse_support.expect_body_error "let table: Map<String, List<Int64>> = [:]"
        ~code:Angle_brackets ~at:"<"
        ~fixed:("Map<String, List<Int64>>", "Map[String, List[Int64]]"));
  Harness.test "fn first<T> in a definition" (fun () ->
      Parse_support.expect_error
        "fn first<Element: Ordered>(items: List[Element]) -> Element { todo }" ~code:Angle_brackets
        ~at:"<"
        ~fixed:("first<Element: Ordered>", "first[Element: Ordered]");
      Parse_support.expect_error "type Box<Item>(item: Item)" ~code:Angle_brackets ~at:"<"
        ~fixed:("Box<Item>", "Box[Item]"));
  Harness.test "a comparison after a type is not angle brackets" (fun () ->
      let _, diagnostics = Parse_support.parse_body "let small = count as Int64 < limit" in
      if Support.list_codes diagnostics <> [ "parser.as_conversion" ] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a comparison in a function type inside angle brackets stays a comparison" (fun () ->
      let _, diagnostics =
        Parse_support.parse_body "let checks: List<(fn(index: UInt64) requires index < 3)> = []"
      in
      if Support.list_codes diagnostics <> [ "parser.angle_brackets" ] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a path written with `::` is parsed as the members it means" (fun () ->
      Parse_support.expect_recovered_statements "let shape = geometry::Shape::Circle"
        [ "(let shape (. (. geometry Shape) Circle))" ];
      Parse_support.expect_recovered_statements "let items = List::<Int64>::new()"
        [ "(let items (call (. error new)))" ]);
  Harness.test "a variant with its type in a pattern" (fun () ->
      Parse_support.expect_body_error Fixtures.Parser_rules.match_on_a_type_qualified_variant
        ~code:Qualified_variant ~at:"Shape." ~fixed:("Shape.Circle", "Circle");
      Parse_support.expect_body_error "let empty = shape is geometry.Shape.Empty"
        ~code:Qualified_variant ~at:"geometry.Shape." ~fixed:("geometry.Shape.Empty", "Empty"));
  Harness.test "a variant with its module in a pattern" (fun () ->
      Parse_support.expect_body_error "let round = shape is geometry.Circle(radius)"
        ~code:Qualified_variant ~at:"geometry." ~fixed:("geometry.Circle", "Circle"));
  Harness.test "a constant of a type in a pattern is not a variant" (fun () ->
      List.iter
        (fun text ->
          let _, diagnostics = Parse_support.parse_body text in
          if Support.list_codes diagnostics <> [] then
            Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)))
        [ "let teapot = status is Status.teapot"; "let teapot = status is http.Status.teapot" ]);
  Harness.test "vec![...]" (fun () ->
      Parse_support.expect_body_error "let items = vec![1, 2]" ~code:Macro_call ~at:"!"
        ~fixed:("vec!", ""));
  Harness.test "println!(...) has no fix" (fun () ->
      Parse_support.expect_body_error "println!(\"total: {}\", total)" ~code:Macro_call ~at:"!");
  Harness.test "todo!()" (fun () ->
      Parse_support.expect_body_error "todo!()" ~code:Macro_call ~at:"!" ~fixed:("todo!()", "todo");
      Parse_support.expect_body_error "unreachable!(\"never\")" ~code:Macro_call ~at:"!");
  Harness.test "a negation after a name is not a macro" (fun () ->
      let _, diagnostics = Parse_support.parse_body "let different = a != (b)" in
      if Support.list_codes diagnostics <> [] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a tuple" (fun () ->
      Parse_support.expect_body_error "let pair = (1, 2)" ~code:Tuple ~at:"(" ~occurrence:2;
      Parse_support.expect_body_error "let first = pair.0" ~code:Tuple ~at:"0";
      Parse_support.expect_body_error "let pair: (Int64, String) = make()" ~code:Tuple ~at:"("
        ~occurrence:2);
  Harness.test "a ** b" (fun () ->
      Parse_support.expect_body_error "let square = x ** 2" ~code:Power_operator ~at:"**";
      Parse_support.expect_recovered_statements "let y = a + x ** 2" [ "(let y (+ a error))" ]);
  Harness.test "name := value" (fun () ->
      Parse_support.expect_body_error "count := 0" ~code:Short_declaration ~at:":="
        ~fixed:("count := 0", "let count = 0");
      Parse_support.expect_body_error "point.x := 0" ~code:Short_declaration ~at:":=");
  Harness.test "value |> function" (fun () ->
      Parse_support.expect_body_error "let total = items |> sum" ~code:Pipe_operator ~at:"|>"
        ~fixed:("items |> sum", "sum(items)");
      Parse_support.expect_body_error "let total = items\n  |> list.sum" ~code:Pipe_operator
        ~at:"|>"
        ~fixed:("let total = items\n  |> list.sum", "let total = list.sum(items)");
      Parse_support.expect_body_error "let total = items |> take(3)" ~code:Pipe_operator ~at:"|>");
  Harness.test "a lambda with a result type" (fun () ->
      Parse_support.expect_body_error "let double = fn(x: Int64) -> Int64 { x * 2 }"
        ~code:Lambda_result_type ~at:" -> Int64" ~fixed:(" -> Int64", ""));
  Harness.test "List<String>.new() in an expression" (fun () ->
      Parse_support.expect_body_error "let names = List<String>.new()" ~code:Angle_brackets ~at:"<"
        ~fixed:("List<String>", "List[String]"));
  Harness.test "a comparison of uppercase names is not angle brackets" (fun () ->
      let _, diagnostics = Parse_support.parse_body "let between = Low < value && value > High" in
      if Support.list_codes diagnostics <> [] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "impl<T>" (fun () ->
      Parse_support.expect_error "impl<Item> Shown for Box[Item] {}" ~code:Impl_parameters ~at:"<"
        ~fixed:("impl<Item>", "impl");
      Parse_support.expect_error "impl<Item: Shown> Shown for Box[Item] {}" ~code:Impl_parameters
        ~at:"<");
  Harness.test "!value is Pattern needs parentheses" (fun () ->
      Parse_support.expect_body_error "let failed = !response is Ok(_)" ~code:Needs_parentheses
        ~at:"is"
        ~fixed:("let failed = !response is Ok(_)", "let failed = !(response is Ok(_))")
        ~alternatives:[ ("!response", "(!response)") ];
      Parse_support.expect_body_error "let off = !flags.ready is true" ~code:Needs_parentheses
        ~at:"is"
        ~fixed:("flags.ready is true", "(flags.ready is true)")
        ~alternatives:[ ("!flags.ready", "(!flags.ready)") ]);
  Harness.test "a negation that is not the whole left operand of is needs none" (fun () ->
      let _, diagnostics = Parse_support.parse_body Fixtures.Parser_rules.negations_around_is in
      if Support.list_codes diagnostics <> [] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "a ?? b" (fun () ->
      Parse_support.expect_body_error "let name = user.name ?? \"guest\"" ~code:Null_coalescing
        ~at:"?"
        ~fixed:("name ?? \"guest\"", "name.unwrap_or(\"guest\")");
      Parse_support.expect_body_error "let port = settings.port ?: 80" ~code:Null_coalescing ~at:"?"
        ~fixed:("port ?: 80", "port.unwrap_or(80)");
      Parse_support.expect_body_error "let total = a + b ?? 0" ~code:Null_coalescing ~at:"?"
        ~fixed:("a + b ?? 0", "(a + b).unwrap_or(0)"));
  Harness.test "a ? after a call is still a try" (fun () ->
      let _, diagnostics =
        Parse_support.parse_body Fixtures.Parser_rules.question_marks_after_calls_and_names
      in
      if Support.list_codes diagnostics <> [] then
        Harness.fail "got [%s]" (String.concat "; " (Support.list_codes diagnostics)));
  Harness.test "items.map { it.name }" (fun () ->
      Parse_support.expect_body_error "let names = items.map { it.name }" ~code:Trailing_lambda
        ~at:"{ it"
        ~fixed:("map { it.name }", "map(fn(item) { item.name })"));
  Harness.test "it in an interpolation is renamed too" (fun () ->
      Parse_support.expect_body_error "let x = items.map { \"${it.name}\" }" ~code:Trailing_lambda
        ~at:"{ \""
        ~fixed:("map { \"${it.name}\" }", "map(fn(item) { \"${item.name}\" })"));
  Harness.test "a trailing lambda followed by more of its line has no fix" (fun () ->
      let _, diagnostics = Parse_support.parse_body "let total = items.map { it.size }.sum()" in
      Harness.expect_strings
        ~expected:[ "parser.trailing_lambda"; "parser.unexpected_token" ]
        (Support.list_codes diagnostics);
      if List.exists (fun (diagnostic : Diagnostic.t) -> diagnostic.fixes <> []) diagnostics then
        Harness.fail "a diagnostic has a fix");
  Harness.test "the lambda's parameter is a plain singular, or element" (fun () ->
      Parse_support.expect_body_error "let x = entries.map { it.key }" ~code:Trailing_lambda
        ~at:"{ it"
        ~fixed:("map { it.key }", "map(fn(entry) { entry.key })");
      Parse_support.expect_body_error "let x = statuses.map { it.code }" ~code:Trailing_lambda
        ~at:"{ it"
        ~fixed:("map { it.code }", "map(fn(element) { element.code })"));
  Harness.test "x as Int64" (fun () ->
      Parse_support.expect_body_error "let n = size as Int64" ~code:As_conversion ~at:"as"
        ~fixed:("size as Int64", "Int64.from_integer(size)")
        ~alternatives:[ ("size as Int64", "Int64.try_from_integer(size)") ]);
  Harness.test "x as Float64" (fun () ->
      Parse_support.expect_body_error "let ratio = count as Float64" ~code:As_conversion ~at:"as"
        ~fixed:("count as Float64", "count.to_float64()"));
  Harness.test "loop" (fun () ->
      Parse_support.expect_body_error "loop {\n  todo\n}" ~code:Reserved_word ~at:"loop"
        ~fixed:("loop", "while true"));
  Harness.test "const" (fun () ->
      Parse_support.expect_error "const pi: Float64 = 3.14" ~code:Reserved_word ~at:"const"
        ~fixed:("const", "let"));
  Harness.test "elif" (fun () ->
      Parse_support.expect_body_error "if a {\n  f()\n}\nelif b {\n  g()\n}" ~code:Elif ~at:"elif"
        ~fixed:("}\nelif b {", "} else if b {"))

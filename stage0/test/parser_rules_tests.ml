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
      definition Fixtures.Parser_rules.clauses_in_the_order_written
        "(fn run_example ((first_number: Int64)) -> Int64 (ensures (> result first_number)) \
         (requires (> first_number 0)) (decreases first_number 1) (uses Clock) (block \
         first_number))");
  test "cost clauses" (fun () ->
      definition Fixtures.Parser_rules.cost_clauses
        "(fn run_example ((visit: (fn (Item) (cost time finite)))) (cost amortized time (O (* \
         (call (. items length)) (call time visit)))) (cost allocations (<= 1)) (cost (calls \
         visit) (== 2)) (cost (calls FileRead.read) (== 3)) (cost (calls FileRead) (== 4)) (cost \
         time finite) (block))");
  test "parsing continues after a misspelled cost word" (fun () ->
      error "fn run_example() cost time fnite {}" ~code:Cost_word ~at:"fnite"
        ~fixed:"fn run_example() cost time finite {}";
      let _, diagnostics = parse "fn run_example() cost tme fnite {}" in
      if codes diagnostics <> [ "parser.cost_word"; "parser.cost_word" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a trait's body on the next line" (fun () ->
      definition Fixtures.Parser_rules.traits_body_on_the_next_line "(trait Payload (type Kappa))");
  test "a misspelled cost word has a fix" (fun () ->
      error "fn run_example() cost allocation == 0 {}" ~code:Cost_word ~at:"allocation"
        ~fixed:"fn run_example() cost allocations == 0 {}");
  test "finite is only for time" (fun () ->
      error "fn run_example() cost allocations finite {}" ~code:Finite_not_time ~at:"finite");
  test "cost potential belongs to a type" (fun () ->
      error "fn run_example() cost potential first_number {}" ~code:Misplaced_potential
        ~at:"potential");
  test "uses appears at most once" (fun () ->
      error "fn run_example() uses Clock uses Random {}" ~code:Repeated_clause ~at:"uses Random");
  test "a missing body gets { todo }" (fun () ->
      error "fn run_example() -> Int64\nfn second_example() {}" ~code:Missing_body
        ~at:"\nfn second_example"
        ~fixed:"fn run_example() -> Int64 { todo }\nfn second_example() {}");
  test "self only in a method" (fun () ->
      error "fn run_example(self) {}" ~code:Misplaced_self ~at:"self");
  test "self only first" (fun () ->
      error "fn Payload.run_example(first_number: Int64, self) {}" ~code:Misplaced_self ~at:"self");
  test "a parameter cannot be named result" (fun () ->
      error "fn run_example(result: Int64) {}" ~code:Reserved_specification_name ~at:"result");
  test "a function cannot be named old" (fun () ->
      error "fn old() {}" ~code:Reserved_specification_name ~at:"old");
  test "types" (fun () ->
      definition "type Point(first_number: Float64, second_number: Float64 = 0.0)"
        "(type Point ((first_number: Float64) (second_number: Float64 (= 0e0))))";
      definition "type DiscardLog()" "(type DiscardLog ())";
      definition "type Bit = Zero | One" "(type Bit (= Zero One))";
      definition "public opaque type Session = todo" "(public opaque (type Session = todo))";
      definition Fixtures.Parser_rules.types
        "(type Tree[Value] (= Leaf (indirect Node ((left: Tree[Value]) (right: Tree[Value])))) \
         (invariant (call is_balanced self)) (derives Equal Hash) (cost potential (call size \
         self)))");
  test "a trait" (fun () ->
      definition Fixtures.Parser_rules.trait
        "(trait Ordered : Equal (type Key: Hash) (law transitive ((first_value: Self) \
         (second_value: Self)) (requires (<= first_value second_value)) (block true)) (fn compare \
         (self (other: Self)) -> Ordering) (fn max (own self (other: own Self)) -> Self (ensures \
         true) (block self)))";
      definition "trait Loggable: Display + Hash {}" "(trait Loggable : Display + Hash)");
  test "an impl" (fun () ->
      definition Fixtures.Parser_rules.impl
        "(impl FileRead for FilesWithin (uses FileRead) (type Error = FileError) (fn read (self) \
         -> Bytes (block todo)))";
      definition "impl Display for List[Element: Display] {}"
        "(impl Display for List[Element: Display])");
  test "an associated capability set" (fun () ->
      definition Fixtures.Parser_rules.associated_capability_set
        "(trait Feed (capability Uses) (fn pull (mut self) -> Int64 (uses Self.Uses)))";
      definition Fixtures.Parser_rules.associated_capability_set_2
        "(impl Feed for Zip[First: Feed, Second: Feed] (capability Uses = First.Uses Second.Uses \
         Clock))";
      definition Fixtures.Parser_rules.associated_capability_set_3
        "(fn drain[Source: Feed] ((source: mut Source)) (uses Source.Uses Clock) (block))";
      definition "fn run(step: (fn() uses Self.Uses)) {}"
        "(fn run ((step: (fn () (uses Self.Uses)))) (block))");
  test "an associated capability set is named after a dot" (fun () ->
      error Fixtures.Parser_rules.associated_capability_set_is_named_after_a_dot
        ~code:Unexpected_token ~at:"\n{";
      error Fixtures.Parser_rules.associated_capability_set_is_named_after_a_dot_2
        ~code:Unexpected_token ~at:"}";
      error "type Point(first_number: Int64)\n  derives Self.Uses" ~code:Unexpected_token ~at:"Self");
  test "a capability" (fun () ->
      definition Fixtures.Parser_rules.capability
        "(capability Clock (fn now () -> Instant) (fn sleep ((duration: Duration))))");
  test "a capability's methods take no self" (fun () ->
      error Fixtures.Parser_rules.capabilitys_methods_take_no_self ~code:Misplaced_self ~at:"self");
  test "an impl's methods need bodies" (fun () ->
      error Fixtures.Parser_rules.impls_methods_need_bodies ~code:Missing_body ~at:"\n}"
        ~fixed:Fixtures.Parser_rules.impls_methods_need_bodies_fixed);
  test "constants" (fun () ->
      definition "public let UInt8.maximum: UInt8 = 255" "(public (let UInt8.maximum : UInt8 255))";
      definition "let pi: Float64 = 3.14" "(let pi : Float64 314e-2)");
  test "a test, a theorem, and a law's proof" (fun () ->
      definition Fixtures.Parser_rules.test_a_theorem_and_a_laws_proof
        "(test \"writes\" (uses FileWrite) (block (assert true)))";
      definition Fixtures.Parser_rules.test_a_theorem_and_a_laws_proof_2
        "(public (theorem keeps[Element] ((items: List[Element])) (ensures true) (block)))";
      definition "proof Monoid.associative for Int64 {\n  lemma()\n}"
        "(proof Monoid.associative for Int64 (block (call lemma)))");
  test "a law's proof names its type as an impl does, with generic parameters" (fun () ->
      definition "proof Ordered.transitive for Box[Item: Ordered] {\n  lemma()\n}"
        "(proof Ordered.transitive for Box[Item: Ordered] (block (call lemma)))";
      error "proof Ordered.transitive for any Shown {}" ~code:Unexpected_token ~at:"any");
  test "a test's name is a plain string" (fun () ->
      error "test \"a${b}\" {}" ~code:Interpolation_not_allowed ~at:"\"a");
  test "an impl takes no visibility" (fun () ->
      error "public impl Alpha for Beta {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:"impl Alpha for Beta {}");
  test "an impl's trait arguments declare no generic parameter, as the recursive type check assumes"
    (fun () -> error "impl Selected[Carried: Shown] for Marker {}" ~code:Unexpected_token ~at:":");
  test "a test takes no visibility" (fun () ->
      error "internal test \"a\" {}" ~code:Misplaced_visibility ~at:"internal"
        ~fixed:"test \"a\" {}");
  test "a law's proof takes no visibility" (fun () ->
      error "public proof Alpha.second_value for Gamma {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:"proof Alpha.second_value for Gamma {}");
  test "only a type is opaque" (fun () ->
      error "public opaque fn run_example() {}" ~code:Misplaced_opaque ~at:"opaque"
        ~fixed:"public fn run_example() {}");
  test "an impl with a visibility and a modifier has one diagnostic" (fun () ->
      error "public opaque impl Alpha for Beta {}" ~code:Misplaced_visibility ~at:"public"
        ~fixed:"impl Alpha for Beta {}")

(* Precedence and combinations that need parentheses *)

let () =
  (* The error points at [at], the operator that cannot take its operand. *)
  let combination text ~at ~code ~fixes =
    match fixes with
    | fixed :: alternatives ->
        body_error ("let first_number = " ^ text) ~code ~at ~fixed:("let first_number = " ^ fixed)
          ~alternatives:(List.map (( ^ ) "let first_number = ") alternatives)
    | [] -> body_error ("let first_number = " ^ text) ~code ~at
  in
  test "bitwise and comparison: Rust's reading, then C's" (fun () ->
      combination "flags & mask == 0" ~at:"==" ~code:Needs_parentheses
        ~fixes:[ "(flags & mask) == 0"; "flags & (mask == 0)" ]);
  test "shift and addition: C and Rust's reading, then Go and Swift's" (fun () ->
      combination "first_value << second_value + 1" ~at:"<<" ~code:Needs_parentheses
        ~fixes:[ "first_value << (second_value + 1)"; "(first_value << second_value) + 1" ]);
  test "& and | read the same everywhere" (fun () ->
      combination "first_value & second_value | third_value" ~at:"|" ~code:Needs_parentheses
        ~fixes:[ "(first_value & second_value) | third_value" ]);
  test "& and | read the same on the right" (fun () ->
      combination "third_value | first_value & second_value" ~at:"|" ~code:Needs_parentheses
        ~fixes:[ "third_value | (first_value & second_value)" ]);
  test "a reading that needs more parentheses inside && gets them" (fun () ->
      combination "first_value & second_value == third_value && fourth_value" ~at:"=="
        ~code:Needs_parentheses
        ~fixes:
          [
            "(first_value & second_value) == third_value && fourth_value";
            "(first_value & (second_value == third_value)) && fourth_value";
          ]);
  test "the other reading takes the operand next to the operator" (fun () ->
      combination "text_value & first_value + second_value + third_value" ~at:"&"
        ~code:Needs_parentheses
        ~fixes:
          [
            "text_value & (first_value + second_value + third_value)";
            "(text_value & first_value) + second_value + third_value";
          ]);
  test "the same bitwise operator chains" (fun () ->
      statement "let first_number = first_value | second_value | third_value"
        "(let first_number (| (| first_value second_value) third_value))");
  test "shifts chain" (fun () ->
      statement "let first_number = first_value << 1 >> 2"
        "(let first_number (>> (<< first_value 1) 2))");
  test "&& and || cannot be mixed" (fun () ->
      combination "first_value && second_value || third_value" ~at:"||" ~code:Needs_parentheses
        ~fixes:
          [
            "(first_value && second_value) || third_value";
            "first_value && (second_value || third_value)";
          ]);
  test "comparisons do not chain" (fun () ->
      combination "first_value < second_value < third_value" ~at:"< third_value"
        ~code:Needs_parentheses
        ~fixes:[ "first_value < second_value && second_value < third_value" ]);
  test "a chained comparison without a simple middle has no fix" (fun () ->
      combination "first_value < run_example(second_value) < third_value" ~at:"< third_value"
        ~code:Needs_parentheses ~fixes:[]);
  test "is does not chain" (fun () ->
      combination "a is B == c" ~at:"==" ~code:Needs_parentheses ~fixes:[]);
  test "ranges do not chain" (fun () ->
      combination "0..10..20" ~at:"..20" ~code:Needs_parentheses ~fixes:[]);
  test "==> does not chain: Dafny's reading first" (fun () ->
      error "fn run_example() requires first_value ==> second_value ==> third_value {}"
        ~code:Needs_parentheses ~at:"==> third_value"
        ~fixed:"fn run_example() requires first_value ==> (second_value ==> third_value) {}"
        ~alternatives:
          [ "fn run_example() requires (first_value ==> second_value) ==> third_value {}" ]);
  test "parentheses settle a combination" (fun () ->
      statement "let first_number = (flags & mask) == 0"
        "(let first_number (== (paren (& flags mask)) 0))");
  test "a quantifier may end && in a specification" (fun () ->
      definition
        "fn run_example() requires first_value && exists first_number in text_value => \
         first_number {}"
        "(fn run_example () (requires (&& first_value (exists (in first_number text_value) \
         first_number))) (block))");
  test "a quantifier elsewhere needs parentheses" (fun () ->
      error "fn run_example() requires count + forall first_number in text_value => first_number {}"
        ~code:Needs_parentheses ~at:"forall"
        ~fixed:
          "fn run_example() requires count + (forall first_number in text_value => first_number) {}");
  test "echo as an operand needs parentheses" (fun () ->
      body_error "let first_number = count + echo first_number" ~code:Needs_parentheses ~at:"echo"
        ~fixed:"let first_number = count + (echo first_number)");
  test "each combination in a chain is reported" (fun () ->
      let _, diagnostics =
        body_of "let first_number = first_value < second_value < third_value < fourth_value"
      in
      if List.length diagnostics <> 2 then fail "got %d diagnostics" (List.length diagnostics))

(* Checks on a whole definition *)

let () =
  test "a quantifier over a range is an expression in code" (fun () ->
      statement "let first_number = forall step_index in text_value => step_index"
        "(let first_number (forall (in step_index text_value) step_index))");
  test "a quantifier over a type in a test" (fun () ->
      error Fixtures.Parser_rules.quantifier_over_a_type_in_a_test ~code:Specification_only
        ~at:"forall");
  test "==> in a test" (fun () ->
      error Fixtures.Parser_rules.in_a_test ~code:Specification_only ~at:"==>");
  test "==> in a constant" (fun () ->
      error "let first_number: Bool = first_value ==> second_value" ~code:Specification_only
        ~at:"==>");
  test "==> and a quantifier over a type in a function's body are left to the type checker"
    (fun () ->
      definition Fixtures.Parser_rules.and_a_quantifier_over_a_type_in_a_functions_body
        "(fn run_example () -> Bool (block (==> first_value (forall value: Int64 (== value \
         value)))))");
  test "a yielding method's parameter cannot be named yielded or finished" (fun () ->
      error Fixtures.Parser_rules.yielding_methods_parameter_cannot_be_named_yielded
        ~code:Reserved_specification_name ~at:"yielded";
      definition "fn run_example(finished: Bool) {}" "(fn run_example ((finished: Bool)) (block))");
  test "a loop's cost clause" (fun () ->
      statement "for row in rows\n  cost time O(yielded.length())\n{}"
        "(for row rows (cost time (O (call (. yielded length)))) (block))");
  test "a loop's cost is not amortized or finite" (fun () ->
      body_error "while first_value\n  cost amortized time O(1)\n{}" ~code:Loop_cost_bound
        ~at:"cost";
      body_error "while first_value\n  cost time finite\n{}" ~code:Loop_cost_bound ~at:"cost");
  test "specifications allow forall" (fun () ->
      definition
        "type Structure(items: List[Int64])\n\
        \  invariant forall step_index in items => step_index > 0"
        "(type Structure ((items: List[Int64])) (invariant (forall (in step_index items) (> \
         step_index 0))))";
      statement "while first_value\n  invariant forall step_index in text_value => step_index\n{}"
        "(while first_value (invariant (forall (in step_index text_value) step_index)) (block))");
  test "assert outside tests and proofs" (fun () ->
      body_error "assert true" ~code:Misplaced_assert ~at:"assert");
  test "assert in a proof block" (fun () ->
      statement "proof {\n  assert true\n}" "(proof (block (assert true)))");
  test "assert in a lambda in a test" (fun () ->
      error Fixtures.Parser_rules.assert_in_a_lambda_in_a_test ~code:Misplaced_assert ~at:"assert");
  test "a proof block outside a function's body" (fun () ->
      error Fixtures.Parser_rules.proof_block_outside_a_functions_body ~code:Misplaced_proof
        ~at:"proof");
  test "yield only in a method that yields" (fun () ->
      body_error "yield 1" ~code:Misplaced_yield ~at:"yield";
      definition Fixtures.Parser_rules.yield_only_in_a_method_that_yields
        "(fn Payload.each (self) yields Int64 (block (yield 1)))");
  test "a method that lends" (fun () ->
      definition Fixtures.Parser_rules.method_that_lends
        "(fn Grid.cell (mut self (position: Position)) lends mut Cell (block (yield (mut ([] (. \
         self cells) 0)))))");
  test "lends own" (fun () ->
      error "fn Payload.part(own self) lends own Part {}" ~code:Lends_own ~at:"own Part"
        ~fixed:"fn Payload.part(own self) lends Part {}");
  test "yield in a lambda" (fun () ->
      error Fixtures.Parser_rules.yield_in_a_lambda ~code:Misplaced_yield ~at:"yield 1");
  test "yield in concurrent code" (fun () ->
      error Fixtures.Parser_rules.yield_in_concurrent_code ~code:Misplaced_yield ~at:"yield 1";
      error Fixtures.Parser_rules.yield_in_concurrent_code_2 ~code:Misplaced_yield
        ~at:"yield first_number");
  test "break outside a loop" (fun () -> body_error "break" ~code:Misplaced_loop_exit ~at:"break");
  test "continue across a lambda" (fun () ->
      body_error "for first_number in text_value {\n  run_example(fn() { continue })\n}"
        ~code:Misplaced_loop_exit ~at:"continue");
  test "break and continue in a loop" (fun () ->
      statement "while true {\n  if first_value { break } else { continue }\n}"
        "(while true (block (if first_value (block break) (block continue))))");
  test "return leaving a parallel block" (fun () ->
      body_error "parallel {\n  return\n}" ~code:Leaves_parallel ~at:"return");
  test "? leaving a parallel for" (fun () ->
      body_error
        "parallel for first_number in text_value {\n\
        \  let second_number = run_example(first_number)?\n\
         }"
        ~code:Leaves_parallel ~at:"?");
  test "break in a parallel for" (fun () ->
      body_error "parallel for first_number in text_value {\n  break\n}" ~code:Leaves_parallel
        ~at:"break");
  test "continue in a parallel for" (fun () ->
      statement "parallel for first_number in text_value {\n  continue\n}"
        "(parallel-for first_number text_value (block continue))");
  test "break leaving a branch" (fun () ->
      body_error "while first_value {\n  parallel {\n    break\n  }\n}" ~code:Leaves_parallel
        ~at:"break");
  test "a loop inside a branch" (fun () ->
      statement "parallel {\n  for first_number in text_value { break }\n}"
        "(parallel (block (for first_number text_value (block break))))");
  test "return in a lambda inside a branch" (fun () ->
      statement "parallel {\n  run_example(fn() { return })\n}"
        "(parallel (block (call run_example (fn () (block (return))))))");
  test "return, ?, and break leaving a concurrent block or loop" (fun () ->
      statement "concurrent {\n  return\n  let second_number = run_example(first_number)?\n}"
        "(concurrent (block (return) (let second_number (? (call run_example first_number)))))";
      statement
        "concurrent for first_number in text_value {\n\
        \  if first_value { break } else { continue }\n\
         }"
        "(concurrent-for first_number text_value (block (if first_value (block break) (block \
         continue))))";
      statement "while first_value {\n  concurrent {\n    break\n  }\n}"
        "(while first_value (block (concurrent (block break))))");
  test "return leaving a parallel block inside a concurrent one" (fun () ->
      body_error "concurrent {\n  parallel {\n    return\n  }\n}" ~code:Leaves_parallel ~at:"return");
  test "echo in a specification" (fun () ->
      error "fn run_example(first_number: Int64) requires echo first_number > 0 {}"
        ~code:Echo_in_specification ~at:"echo");
  test "a statement rule applies in every block" (fun () ->
      body_error Fixtures.Parser_rules.statement_rule_applies_in_every_block ~code:Misplaced_assert
        ~at:"assert");
  test "echo in a proof" (fun () ->
      body_error "proof {\n  echo first_number\n}" ~code:Echo_in_specification ~at:"echo")

(* Recovery *)

let () =
  test "an error in a statement leaves the next one parsed" (fun () ->
      let statements, diagnostics = body_of "let first_number = 1 2 3\nlet second_number = 2" in
      if codes diagnostics <> [ "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      if List.map Syntax_print.statement statements <> [ "error"; "(let second_number 2)" ] then
        fail "wrong statements");
  test "each bad item in brackets gets its own error" (fun () ->
      let statements, diagnostics =
        body_of
          "run_example(1 +, first_number, 2 3, second_example(first_value second_value))\n\
           let second_number = 2"
      in
      if
        codes diagnostics
        <> [ "parser.unexpected_token"; "parser.unexpected_token"; "parser.unexpected_token" ]
      then fail "got [%s]" (String.concat "; " (codes diagnostics));
      if
        List.map Syntax_print.statement statements
        <> [
             "(call run_example error first_number error (call second_example error))";
             "(let second_number 2)";
           ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "an error in a clause leaves the body parsed" (fun () ->
      let file, diagnostics =
        parse Fixtures.Parser_rules.error_in_a_clause_leaves_the_body_parsed
      in
      if codes diagnostics <> [ "parser.unexpected_token" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics));
      match file.definitions with
      | [ { value; _ } ] ->
          if
            Syntax_print.For_testing.definition value
            <> "(fn run_example () error (ensures true) (block first_number))"
          then fail "got %s" (Syntax_print.For_testing.definition value)
      | _ -> fail "wrong definitions");
  test "an error in a member leaves the next member parsed" (fun () ->
      let file, diagnostics =
        parse Fixtures.Parser_rules.error_in_a_member_leaves_the_next_member_parsed
      in
      ignore file;
      if List.length diagnostics > 2 then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "nothing is reported before a closer the lexer inserted" (fun () ->
      let _, diagnostics =
        parse Fixtures.Parser_rules.nothing_is_reported_before_a_closer_the_lexer
      in
      if codes diagnostics <> [ "lexer.unclosed_bracket" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a reserved word is reported as reserved" (fun () ->
      error "fn run_example[Payload]() where Payload: Hash {}" ~code:Reserved_word ~at:"where")

(* Syntax from other languages *)

let () =
  test "i++" (fun () -> body_error "count++" ~code:Increment ~at:"++" ~fixed:"count += 1");
  test "i--" (fun () -> body_error "items[0]--" ~code:Increment ~at:"--" ~fixed:"items[0] -= 1");
  test "--x" (fun () ->
      body_error "let second_number = --first_number" ~code:Double_negation ~at:"--"
        ~fixed:"let second_number = -(-first_number)");
  test "a comma after a match arm" (fun () ->
      body_error "match first_value {\n  Alpha => 1,\n  Beta => 2\n}" ~code:Match_arm_comma ~at:","
        ~fixed:"match first_value {\n  Alpha => 1\n  Beta => 2\n}");
  test "x ? a : b" (fun () ->
      body_error "let second_number = ready ? first : second" ~code:Conditional_operator ~at:"?"
        ~fixed:"let second_number = if ready { first } else { second }");
  test "x ? a : b takes the whole left side as the condition" (fun () ->
      body_error "let larger = first_value > second_value ? first_value : second_value"
        ~code:Conditional_operator ~at:"?"
        ~fixed:"let larger = if first_value > second_value { first_value } else { second_value }");
  test "let mut" (fun () ->
      body_error "let mut count = 0" ~code:Let_mut ~at:"mut" ~fixed:"var count = 0");
  test "&x" (fun () ->
      body_error "run_example(&first_number)" ~code:Address_of ~at:"&"
        ~fixed:"run_example(first_number)");
  test "& between two names" (fun () ->
      body_error "match& value {\n  _ => todo\n}" ~code:Address_of ~at:"&"
        ~fixed:"match value {\n  _ => todo\n}");
  test "&mut x" (fun () ->
      body_error "sort(&mut items)" ~code:Address_of ~at:"&" ~fixed:"sort(mut items)");
  test "|x| x + 1" (fun () ->
      body_error "let run_example = items.map(|item| item + 1)" ~code:Closure_bars ~at:"|"
        ~fixed:"let run_example = items.map(fn(item) { item + 1 })");
  test "|x| with a block" (fun () ->
      body_error "let run_example = items.map(|item| { item })" ~code:Closure_bars ~at:"|"
        ~fixed:"let run_example = items.map(fn(item) { item })");
  test "|x| before let ... else" (fun () ->
      body_error Fixtures.Parser_rules.x_before_let_else ~code:Closure_bars ~at:"||"
        ~fixed:Fixtures.Parser_rules.x_before_let_else_fixed);
  test "|| x" (fun () ->
      body_error "let run_example = run(|| 1)" ~code:Closure_bars ~at:"||"
        ~fixed:"let run_example = run(fn() { 1 })");
  test "Point { x: 1.0 }" (fun () ->
      body_error "let probe_point = Point { first_number: 1.0, second_number: 2.0 }"
        ~code:Brace_record ~at:"{ first_number"
        ~fixed:"let probe_point = Point(first_number: 1.0, second_number: 2.0)");
  test "parse::<Int64>(text)" (fun () ->
      body_error "let limit_count = parse::<Int64>(text)" ~code:Turbofish ~at:"<"
        ~fixed:"let limit_count = parse[Int64](text)");
  test "List<String> in a type" (fun () ->
      body_error "let names: List<String> = []" ~code:Angle_brackets ~at:"<"
        ~fixed:"let names: List[String] = []";
      body_error "let table: Map<String, List<Int64>> = [:]" ~code:Angle_brackets ~at:"<"
        ~fixed:"let table: Map[String, List[Int64]] = [:]");
  test "fn first<T> in a definition" (fun () ->
      error "fn first<Element: Ordered>(items: List[Element]) -> Element { todo }"
        ~code:Angle_brackets ~at:"<"
        ~fixed:"fn first[Element: Ordered](items: List[Element]) -> Element { todo }";
      error "type Box<Item>(item: Item)" ~code:Angle_brackets ~at:"<"
        ~fixed:"type Box[Item](item: Item)");
  test "List<String> is parsed as the brackets it means" (fun () ->
      let statements, _ = body_of "let table: Map<String, List<Int64>> = [:]" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let table : Map[String, List[Int64]] (map))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "a comparison after a type is not angle brackets" (fun () ->
      let _, diagnostics = body_of "let small = count as Int64 < limit" in
      if codes diagnostics <> [ "parser.as_conversion" ] then
        fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "Shape::Circle" (fun () ->
      body_error "let shape = Shape::Circle(radius: 1.0)" ~code:Path_separator ~at:"::"
        ~fixed:"let shape = Shape.Circle(radius: 1.0)";
      body_error "let items = List::new()" ~code:Path_separator ~at:"::"
        ~fixed:"let items = List.new()");
  test "Shape::Circle is parsed as the member it means" (fun () ->
      let statements, _ = body_of "let shape = geometry::Shape::Circle" in
      if List.map Syntax_print.statement statements <> [ "(let shape (. geometry::Shape Circle))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "a variant with its type in a pattern" (fun () ->
      body_error Fixtures.Parser_rules.variant_with_its_type_in_a_pattern ~code:Qualified_variant
        ~at:"Shape." ~fixed:Fixtures.Parser_rules.variant_with_its_type_in_a_pattern_fixed;
      body_error "let empty = shape is geometry::Shape::Empty" ~code:Qualified_variant
        ~at:"geometry::Shape::" ~fixed:"let empty = shape is Empty");
  test "a constant of a type in a pattern is not a variant" (fun () ->
      let _, diagnostics = body_of "let teapot = status is Status.teapot" in
      if codes diagnostics <> [] then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "vec![...]" (fun () ->
      body_error "let items = vec![1, 2]" ~code:Macro_call ~at:"!" ~fixed:"let items = [1, 2]");
  test "println!(...) has no fix" (fun () ->
      body_error "println!(\"total: {}\", total)" ~code:Macro_call ~at:"!");
  test "todo!()" (fun () ->
      body_error "todo!()" ~code:Macro_call ~at:"!" ~fixed:"todo";
      body_error "unreachable!(\"never\")" ~code:Macro_call ~at:"!");
  test "a negation after a name is not a macro" (fun () ->
      let _, diagnostics = body_of "let different = first_value != (second_value)" in
      if codes diagnostics <> [] then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a tuple" (fun () ->
      body_error "let pair = (1, 2)" ~code:Tuple ~at:"(" ~occurrence:2;
      body_error "let first = pair.0" ~code:Tuple ~at:"0";
      body_error "let pair: (Int64, String) = make()" ~code:Tuple ~at:"(" ~occurrence:2);
  test "a ** b" (fun () ->
      body_error "let square = first_number ** 2" ~code:Power_operator ~at:"**";
      let statements, _ = body_of "let second_number = first_value + first_number ** 2" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let second_number (+ first_value (* first_number 2)))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "name := value" (fun () ->
      body_error "count := 0" ~code:Short_declaration ~at:":=" ~fixed:"let count = 0";
      body_error "point.first_number := 0" ~code:Short_declaration ~at:":=";
      let statements, _ = body_of "count := 0" in
      if List.map Syntax_print.statement statements <> [ "(let count 0)" ] then
        fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "value |> function" (fun () ->
      body_error "let total = items |> sum" ~code:Pipe_operator ~at:"|>"
        ~fixed:"let total = sum(items)";
      body_error "let total = items\n  |> list::sum" ~code:Pipe_operator ~at:"|>"
        ~fixed:"let total = list::sum(items)";
      body_error "let total = items |> take(3)" ~code:Pipe_operator ~at:"|>";
      let statements, _ = body_of "let total = items |> sum" in
      if List.map Syntax_print.statement statements <> [ "(let total (call sum items))" ] then
        fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "a lambda with annotations" (fun () ->
      body_error "let double = fn(first_number: Int64) { first_number * 2 }" ~code:Lambda_annotation
        ~at:": Int64" ~fixed:"let double = fn(first_number) { first_number * 2 }";
      body_error "let double = fn(first_number) -> Int64 { first_number * 2 }"
        ~code:Lambda_annotation ~at:" -> Int64"
        ~fixed:"let double = fn(first_number) { first_number * 2 }");
  test "List<String>.new() in an expression" (fun () ->
      body_error "let names = List<String>.new()" ~code:Angle_brackets ~at:"<"
        ~fixed:"let names = List[String].new()";
      let statements, _ = body_of "let names = List<String>.new()" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let names (call (. ([] List String) new)))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "a comparison of uppercase names is not angle brackets" (fun () ->
      let _, diagnostics = body_of "let between = Low < value && value > High" in
      if codes diagnostics <> [] then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "impl<T>" (fun () ->
      error "impl<Item> Shown for Box[Item] {}" ~code:Impl_parameters ~at:"<"
        ~fixed:"impl Shown for Box[Item] {}";
      error "impl<Item: Shown> Shown for Box[Item] {}" ~code:Impl_parameters ~at:"<");
  test "!value is Pattern needs parentheses" (fun () ->
      body_error "let failed = !response is Ok(_)" ~code:Needs_parentheses ~at:"is"
        ~fixed:"let failed = !(response is Ok(_))"
        ~alternatives:[ "let failed = (!response) is Ok(_)" ];
      body_error "let off = !flags.ready is true" ~code:Needs_parentheses ~at:"is"
        ~fixed:"let off = !(flags.ready is true)"
        ~alternatives:[ "let off = (!flags.ready) is true" ]);
  test "a negation that is not the whole left operand of is needs none" (fun () ->
      let _, diagnostics =
        body_of Fixtures.Parser_rules.negation_that_is_not_the_whole_left_operand_of_is
      in
      if codes diagnostics <> [] then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "a ?? b" (fun () ->
      body_error "let name = user.name ?? \"guest\"" ~code:Null_coalescing ~at:"?"
        ~fixed:"let name = user.name.unwrap_or(\"guest\")";
      body_error "let port = settings.port ?: 80" ~code:Null_coalescing ~at:"?"
        ~fixed:"let port = settings.port.unwrap_or(80)";
      body_error "let total = first_value + second_value ?? 0" ~code:Null_coalescing ~at:"?"
        ~fixed:"let total = (first_value + second_value).unwrap_or(0)";
      let statements, _ = body_of "let port = settings.port ?? 80" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let port (call (. (. settings port) unwrap_or) 80))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "a ? after a call is still a try" (fun () ->
      let _, diagnostics = body_of Fixtures.Parser_rules.after_a_call_is_still_a_try in
      if codes diagnostics <> [] then fail "got [%s]" (String.concat "; " (codes diagnostics)));
  test "items.map { it.name }" (fun () ->
      body_error "let names = items.map { it.name }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let names = items.map(fn(item) { item.name })");
  test "it in an interpolation is renamed too" (fun () ->
      body_error "let first_number = items.map { \"${it.name}\" }" ~code:Trailing_lambda ~at:"{ \""
        ~fixed:"let first_number = items.map(fn(item) { \"${item.name}\" })");
  test "the lambda's parameter is a plain singular, or element" (fun () ->
      body_error "let first_number = entries.map { it.key }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let first_number = entries.map(fn(entry) { entry.key })";
      body_error "let first_number = statuses.map { it.code }" ~code:Trailing_lambda ~at:"{ it"
        ~fixed:"let first_number = statuses.map(fn(element) { element.code })");
  test "items.map { it.name } is parsed as the call its fix writes" (fun () ->
      let statements, _ = body_of "let names = items.map { it.name }" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let names (call (. items map) (fn (item) (block (. item name)))))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "parse::<List[Int64]> is parsed as the brackets it means" (fun () ->
      let statements, _ = body_of "let limit_count = parse::<List[Int64]>(text)" in
      if
        List.map Syntax_print.statement statements
        <> [ "(let limit_count (call ([] parse ([] List Int64)) text))" ]
      then fail "got [%s]" (String.concat "; " (List.map Syntax_print.statement statements)));
  test "x as Int64" (fun () ->
      body_error "let limit_count = size as Int64" ~code:As_conversion ~at:"as"
        ~fixed:"let limit_count = Int64.from(size)"
        ~alternatives:[ "let limit_count = Int64.try_from(size)" ]);
  test "loop" (fun () ->
      body_error "loop {\n  todo\n}" ~code:Reserved_word ~at:"loop" ~fixed:"while true {\n  todo\n}");
  test "const" (fun () ->
      error "const pi: Float64 = 3.14" ~code:Reserved_word ~at:"const"
        ~fixed:"let pi: Float64 = 3.14");
  test "elif" (fun () ->
      body_error "if first_value {\n  run_example()\n}\nelif second_value {\n  second_example()\n}"
        ~code:Elif ~at:"elif"
        ~fixed:"if first_value {\n  run_example()\n} else if second_value {\n  second_example()\n}")

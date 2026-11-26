let check_file database file =
  match
    Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database file
  with
  | [] -> Support.list_proof_diagnostics database file
  | errors -> errors

let check packages = check_file (Support.make_database packages)
let expect_proven text = Support.expect_no_diagnostics ~check [ ("app.main", text) ]
let expect_not_proven = Support.expect_one_diagnostic ~check

let list_codes text =
  let packages = Support.setup [ ("app.main", text) ] in
  Support.list_codes (check packages (Support.parse_file "app.main"))

let expect_codes = Support.expect_codes ~check

let list_termination_messages text =
  let packages = Support.setup [ ("app.main", text) ] in
  List.filter_map
    (fun (diagnostic : Diagnostic.t) ->
      if Diagnostic.Code.name diagnostic.code = "prover.termination" then Some diagnostic.message
      else None)
    (check packages (Support.parse_file "app.main"))

let expect_one_termination_failure ~says text =
  match list_termination_messages text with
  | [ message ] ->
      if not (String.includes ~affix:says message) then
        Harness.fail "expected a message that says %S, got: %s" says message
  | messages -> Harness.fail "%d termination failures" (List.length messages)

let list_diagnostics text =
  check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main")

let read_message text =
  let packages = Support.setup [ ("app.main", text) ] in
  match check packages (Support.parse_file "app.main") with
  | [ diagnostic ] -> diagnostic.message
  | actual ->
      Printf.sprintf "%d diagnostics: %s" (List.length actual)
        (String.concat "; " (Support.list_codes actual))

let () =
  Harness.test "an addition that can overflow" (fun () ->
      expect_not_proven Fixtures.Prover.addition_that_can_overflow "prover.overflow"
        ~fixed:
          ( "fn f(count: UInt8) -> UInt8 {",
            "fn f(count: UInt8) -> UInt8\n  requires count <= UInt8.maximum - 1\n{" )
        ~alternatives:
          [ ("fn f(count: UInt8) -> UInt8 {", "fn f(count: UInt8) -> UInt8\n  uses Panic\n{") ]);
  Harness.test "an obligation that the solver runs out of steps on says so" (fun () ->
      let actual = read_message Fixtures.Prover.sum_of_two_cubes in
      if not (String.includes ~affix:"reached its step limit" actual) then
        Harness.fail "message %S" actual);
  Harness.test "code generic over an integer trait is proven for each type that implements it"
    (fun () ->
      expect_proven Fixtures.Prover.twice_of_a_signed_integer;
      let actual = read_message Fixtures.Prover.twice_of_an_unsigned_integer in
      if not (String.includes ~affix:"`Number` is `UInt8`" actual) then
        Harness.fail "message %S" actual);
  Harness.test "a requires rules out the overflow" (fun () ->
      expect_proven Fixtures.Prover.increment_bounded_by_the_requires);
  Harness.test
    "a requires clause read from its code holds or fails at a call as the clause written does"
    (fun () ->
      expect_proven Fixtures.Prover.clamp_with_a_positive_fallback;
      expect_not_proven Fixtures.Prover.clamp_with_a_negative_fallback "prover.requires");
  Harness.test "a name that `is` binds in an `&&` is read by the operands after it" (fun () ->
      expect_proven Fixtures.Prover.converted_result);
  Harness.test "a check in an if rules out the overflow" (fun () ->
      expect_proven Fixtures.Prover.increment_checked_by_an_if);
  Harness.test "a division by a value that may be zero" (fun () ->
      expect_not_proven Fixtures.Prover.division_by_a_value_that_may_be_zero "prover.division"
        ~fixed:
          ( "fn f(value: UInt32, divisor: UInt32) -> UInt32 {",
            "fn f(value: UInt32, divisor: UInt32) -> UInt32\n  requires divisor != 0\n{" )
        ~alternatives:
          [
            ( "fn f(value: UInt32, divisor: UInt32) -> UInt32 {",
              "fn f(value: UInt32, divisor: UInt32) -> UInt32\n  uses Panic\n{" );
          ]);
  Harness.test "a signed division by -1 can overflow" (fun () ->
      expect_not_proven Fixtures.Prover.signed_division_by_an_unchecked_divisor "prover.overflow"
        ~fixed:
          ( "requires divisor != 0\n{\n  value / divisor",
            "requires divisor != 0\n\
            \  requires value != Int64.minimum || divisor != -1\n\
             {\n\
            \  value / divisor" )
        ~alternatives:[ ("requires divisor != 0", "uses Panic\n  requires divisor != 0") ]);
  Harness.test "a signed division rounds toward zero" (fun () ->
      expect_proven Fixtures.Prover.quotient_ensured_rounded_toward_zero;
      expect_not_proven Fixtures.Prover.quotient_ensured_rounded_down "prover.ensures");
  Harness.test "a remainder has the sign of its left operand" (fun () ->
      expect_proven Fixtures.Prover.remainder_of_negative_seven);
  Harness.test "a specification divides `Integer`s toward zero, as code divides integers" (fun () ->
      expect_proven Fixtures.Prover.specification_division_toward_zero;
      expect_not_proven Fixtures.Prover.specification_division_rounded_down "prover.ensures");
  Harness.test "a shift amount must be less than the width" (fun () ->
      expect_not_proven Fixtures.Prover.shift_by_an_unbounded_amount "prover.shift"
        ~fixed:
          ( "fn f(value: UInt32, amount: UInt32) -> UInt32 {",
            "fn f(value: UInt32, amount: UInt32) -> UInt32\n  requires amount < 32\n{" )
        ~alternatives:
          [
            ( "fn f(value: UInt32, amount: UInt32) -> UInt32 {",
              "fn f(value: UInt32, amount: UInt32) -> UInt32\n  uses Panic\n{" );
          ]);
  Harness.test "negating the least signed value overflows" (fun () ->
      expect_not_proven Fixtures.Prover.negation_of_an_int8 "prover.overflow"
        ~fixed:
          ( "fn f(value: Int8) -> Int8 {",
            "fn f(value: Int8) -> Int8\n  requires value != Int8.minimum\n{" )
        ~alternatives:
          [ ("fn f(value: Int8) -> Int8 {", "fn f(value: Int8) -> Int8\n  uses Panic\n{") ]);
  Harness.test "an unreachable that can be reached" (fun () ->
      expect_not_proven Fixtures.Prover.unreachable_that_can_be_reached "prover.unreachable");
  Harness.test "an unreachable after a check" (fun () ->
      expect_proven Fixtures.Prover.unreachable_after_a_check);
  Harness.test "an overflow offers a guard, the checked operation, `requires`, or `uses Panic`"
    (fun () ->
      let actual = read_message Fixtures.Prover.addition_that_can_overflow in
      if
        not
          (String.includes
             ~affix:"It can also be checked first with an `if`, or done with the checked operation."
             actual)
      then Harness.fail "message %S" actual;
      Support.expect_one_diagnostic ~check Fixtures.Prover.addition_that_can_overflow
        "prover.overflow" ~at:("count + 1", 1)
        ~fixed:
          ( "fn f(count: UInt8) -> UInt8 {",
            "fn f(count: UInt8) -> UInt8\n  requires count <= UInt8.maximum - 1\n{" )
        ~alternatives:
          [ ("fn f(count: UInt8) -> UInt8 {", "fn f(count: UInt8) -> UInt8\n  uses Panic\n{") ]);
  Harness.test "the `uses Panic` fix joins the function's `uses` clause" (fun () ->
      Support.expect_one_diagnostic ~check Fixtures.Prover.overflow_in_a_function_with_other_clauses
        "prover.overflow" ~at:("value + 1", 1)
        ~fixed:
          ( "ensures true\n{\n  value + 1",
            "ensures true\n  requires value <= UInt8.maximum - 1\n{\n  value + 1" )
        ~alternatives:[ ("Clock", "Clock, Panic") ]);
  Harness.test "a function that declares `uses Panic` lets its integer operations panic" (fun () ->
      expect_codes Fixtures.Prover.failing_operations_of_a_function_that_may_panic
        [
          "prover.out_of_bounds";
          "prover.out_of_bounds";
          "prover.requires";
          "prover.requires";
          "prover.requires";
        ]);
  Harness.test "a function that uses `Panic unless` a bound proves its operations where it holds"
    (fun () ->
      expect_not_proven Fixtures.Prover.operation_that_panics_unless_a_bound_holds "prover.overflow"
        ~fixed:
          ( "uses Panic unless Tag: Checked\n{\n  value + 1",
            "uses Panic unless Tag: Checked\n\
            \  requires value <= UInt8.maximum - 1 when Tag: Checked\n\
             {\n\
            \  value + 1" );
      expect_proven Fixtures.Prover.operation_proven_where_a_bound_holds);
  Harness.test "expect returns the payload of an Option or a Result" (fun () ->
      expect_proven Fixtures.Prover.payloads_through_expect);
  Harness.test "expect lends the payload of an Option it is lent" (fun () ->
      expect_proven Fixtures.Prover.elements_lent_through_expect);
  Harness.test "a test that declares `Panic` lets its integer operations panic, as a function does"
    (fun () ->
      expect_codes Fixtures.Prover.test_indexing_by_a_sum_from_a_loop [ "prover.out_of_bounds" ]);
  Harness.test "a lambda passed as a function type without `Panic` proves its operations" (fun () ->
      match
        check
          (Support.setup
             [ ("app.main", Fixtures.Prover.overflow_in_a_lambda_of_a_function_that_may_panic) ])
          (Support.parse_file "app.main")
      with
      | [ diagnostic ] ->
          if
            (not (String.includes ~affix:"may overflow `UInt8`" diagnostic.message))
            || List.exists
                 (fun (fix : Source.span Diagnostic.fix) -> fix.title = "Add `uses Panic`")
                 diagnostic.fixes
          then Harness.fail "message %S" diagnostic.message
      | diagnostics -> Harness.fail "%s" (String.concat ", " (Support.list_codes diagnostics)));
  Harness.test "a lambda whose capabilities are inferred takes `Panic` for an operation that fails"
    (fun () ->
      expect_proven Fixtures.Prover.overflow_in_a_lambda_passed_where_its_capabilities_are_inferred;
      expect_not_proven Fixtures.Prover.overflow_in_a_lambda_of_a_function_without_panic
        "prover.overflow");
  Harness.test "a lambda in a test proves its operations" (fun () ->
      expect_not_proven Fixtures.Prover.overflow_in_a_lambda_of_a_test "prover.overflow");
  Harness.test "an index through a bound is proven in a function that declares `uses Panic`"
    (fun () ->
      expect_not_proven Fixtures.Prover.index_through_a_bound_of_a_function_that_may_panic
        "prover.requires"
        ~fixed:
          ( "uses Panic\n{\n  inspect(collection[key])",
            "uses Panic\n  requires collection.contains_key(key)\n{\n  inspect(collection[key])" ));
  Harness.test "an unreachable is proven in a function that declares `uses Panic`" (fun () ->
      expect_not_proven Fixtures.Prover.unreachable_of_a_function_that_may_panic
        "prover.unreachable")

let () =
  Harness.test "a call must meet its callee's requires" (fun () ->
      expect_not_proven Fixtures.Prover.call_outside_its_callees_requires "prover.requires");
  Harness.test "a call that meets its callee's requires" (fun () ->
      expect_proven Fixtures.Prover.call_within_its_callees_requires);
  Harness.test "an ensures is shown" (fun () -> expect_proven Fixtures.Prover.absolute_value);
  Harness.test "an ensures that does not hold" (fun () ->
      expect_not_proven Fixtures.Prover.identity_ensured_larger "prover.ensures");
  Harness.test "an ensures holds at an early return" (fun () ->
      expect_not_proven Fixtures.Prover.early_return_of_a_negative "prover.ensures"
        ~fixed:
          ( "ensures result >= 0\n{\n  if value < 0 { return value }",
            "ensures result >= 0\n  requires value >= 0\n{\n  if value < 0 { return value }" ));
  Harness.test "a callee's ensures is a fact after the call" (fun () ->
      expect_proven Fixtures.Prover.bump_ensures_after_the_call);
  Harness.test "a mut argument is mutated only through the callee's ensures" (fun () ->
      expect_not_proven Fixtures.Prover.touch_without_an_ensures "prover.ensures")

let () =
  Harness.test "constants whose values read each other are an error at each of them" (fun () ->
      match list_codes "let first: Int64 = second + 1\nlet second: Int64 = first + 1\n" with
      | [ "prover.constant_cycle"; "prover.constant_cycle" ] -> ()
      | found -> Harness.fail "found [%s]" (String.concat "; " found));
  Harness.test "a constant whose value reads itself is an error" (fun () ->
      expect_not_proven "let count: Int64 = count + 1\n" "prover.constant_cycle"
        ~says:"This reads `app.main.count` in its own value" ~at:("count", 2));
  Harness.test "a constant built with a field default that reads the constant is an error"
    (fun () ->
      expect_not_proven
        "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1)\n"
        "prover.constant_cycle" ~says:"leaves out the field `y`, whose default reads");
  Harness.test
    "a constant built by a call that omits an argument whose default reads it is an error"
    (fun () ->
      expect_not_proven "fn scale(by: Int64 = limit) -> Int64 { by }\nlet limit: Int64 = scale()\n"
        "prover.constant_cycle"
        ~says:
          "This leaves out the argument `by`, whose default reads `app.main.limit`, so \
           `app.main.limit` would be computed from itself."
        ~at:("scale()", 1));
  Harness.test "a constant that sets the field whose default reads the constant is fine" (fun () ->
      expect_proven
        "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1, y: 2)\n");
  Harness.test "a constant whose value calls a function that reads the constant is an error"
    (fun () ->
      expect_not_proven Fixtures.Prover.constant_read_by_the_function_it_calls
        "prover.constant_cycle"
        ~says:
          "This calls `next_after_limit`, whose code depends on `app.main.limit`, so \
           `app.main.limit` would be computed from itself."
        ~at:("next_after_limit()", 2));
  Harness.test "a constant read by an impl that its value passes to generic code is an error"
    (fun () ->
      expect_not_proven Fixtures.Prover.constant_read_by_the_impl_it_supplies
        "prover.constant_cycle" ~says:"This uses `Coin.weight`, whose code depends on");
  Harness.test "a call in a constant's value meets its callee's requires" (fun () ->
      expect_not_proven Fixtures.Prover.constant_calling_outside_a_requires "prover.requires")

let () =
  let expect_circular = Support.expect_one_diagnostic ~check in
  let expect_circular_at_each text ~says =
    let diagnostics = list_diagnostics text in
    if
      List.length diagnostics <> List.length says
      || not
           (List.for_all2
              (fun (diagnostic : Diagnostic.t) affix ->
                Diagnostic.Code.name diagnostic.code = "prover.circular_proof"
                && String.includes ~affix diagnostic.message)
              diagnostics says)
    then
      Harness.fail "found [%s]"
        (String.concat "; "
           (List.map
              (fun (diagnostic : Diagnostic.t) ->
                Diagnostic.Code.name diagnostic.code ^ ": " ^ diagnostic.message)
              diagnostics))
  in
  Harness.test "an invariant that calls a method of its type is an error" (fun () ->
      expect_circular Fixtures.Prover.invariant_calling_a_method_of_its_type "prover.circular_proof"
        ~says:
          "This calls `Counter.value`, whose proof depends on the invariant of `Counter`, so the \
           invariant would be proven from itself."
        ~at:("self.value()", 1));
  Harness.test "an invariant that calls a function that builds a value of its type is an error"
    (fun () ->
      expect_circular Fixtures.Prover.invariant_calling_a_function_that_builds_its_type
        "prover.circular_proof"
        ~says:"This calls `through`, whose proof depends on the invariant of `Counter`"
        ~at:("through(count)", 1));
  Harness.test "an invariant that reaches a user of its type through a call is an error" (fun () ->
      expect_circular Fixtures.Prover.invariant_calling_a_function_that_reaches_a_user_of_its_type
        "prover.circular_proof"
        ~says:"This calls `bound`, whose proof depends on the invariant of `Counter`"
        ~at:("bound()", 1));
  Harness.test "an invariant that reaches a user of its type through a contract is an error"
    (fun () ->
      expect_circular
        Fixtures.Prover.invariant_calling_a_function_whose_contract_calls_a_user_of_its_type
        "prover.circular_proof"
        ~says:"This calls `stated`, whose proof depends on the invariant of `Counter`"
        ~at:("stated(count)", 1));
  Harness.test "invariants of two types that build each other are an error at each type" (fun () ->
      expect_circular_at_each Fixtures.Prover.invariants_of_two_types_that_build_each_other
        ~says:
          [
            "This calls `Gauge.read`, whose proof depends on the invariant of `Counter`";
            "This calls `Counter.value`, whose proof depends on the invariant of `Gauge`";
          ]);
  Harness.test "an invariant that calls a method of an element of its own type is an error"
    (fun () ->
      expect_circular Fixtures.Prover.invariant_calling_a_method_of_an_element_of_its_type
        "prover.circular_proof" ~says:"This calls `Chain.head`" ~at:("rest[0].head()", 1));
  Harness.test "a law proof that assumes laws proven from its own law is an error" (fun () ->
      expect_circular Fixtures.Prover.law_proof_calling_a_method_of_a_trait_that_requires_its_own
        "prover.circular_proof" ~says:"This assumes the laws of `Ordered` for `Level`"
        ~at:("value.compare(value)", 1));
  Harness.test "a theorem that a law proof calls is proven without the laws of that impl" (fun () ->
      expect_not_proven Fixtures.Prover.law_proven_by_a_theorem_that_needs_the_law "prover.ensures");
  Harness.test "a law is not proven through a generic impl that assumes its bound's laws" (fun () ->
      expect_codes Fixtures.Prover.law_proven_through_a_generic_impl_that_assumes_it
        [ "prover.circular_proof" ]);
  Harness.test "a law is not proven through a generic function that assumes its bound's laws"
    (fun () ->
      expect_codes Fixtures.Prover.law_proven_through_a_generic_function_that_assumes_it
        [ "prover.circular_proof" ]);
  Harness.test "an invariant may call a function of a field's type" (fun () ->
      expect_proven Fixtures.Prover.invariant_calling_a_function_of_a_field);
  Harness.test "a requires that calls its own function is an error, and its caller is read"
    (fun () ->
      expect_circular Fixtures.Prover.requires_calling_its_own_function "prover.circular_proof"
        ~says:"This calls `clamp` in its own contract, so the contract would be proven from itself."
        ~at:("clamp(n)", 1));
  Harness.test "an ensures that calls its own function is an error" (fun () ->
      expect_circular Fixtures.Prover.ensures_calling_its_own_function "prover.circular_proof"
        ~says:"This calls `clamp` in its own contract" ~at:("clamp(n)", 1));
  Harness.test "contracts of two functions that call each other are an error at each" (fun () ->
      expect_circular_at_each Fixtures.Prover.contracts_of_two_functions_that_call_each_other
        ~says:
          [
            "This calls `second`, whose proof depends on the contract of `first`";
            "This calls `first`, whose proof depends on the contract of `second`";
          ]);
  Harness.test
    "a contract that a method takes from its trait is an error where it calls a method whose \
     contract calls back" (fun () ->
      expect_circular_at_each
        Fixtures.Prover.contract_from_a_trait_calling_a_method_whose_contract_calls_back
        ~says:
          [
            "This calls `Marker.measure`, whose proof depends on the contract of `Marker.limit`";
            "The contract that this method takes from its trait calls `Marker.limit`, whose proof \
             depends on the contract of `Marker.measure`, so the contract would be proven from \
             itself.";
          ]);
  Harness.test "a recursive function's ensures may call the function" (fun () ->
      expect_proven Fixtures.Prover.recursive_function_whose_ensures_calls_itself);
  Harness.test
    "a recursive function's contract is assumed in its own proof only below the entry measure"
    (fun () ->
      expect_not_proven Fixtures.Prover.recursive_function_whose_ensures_contradicts_itself
        "prover.termination";
      expect_codes Fixtures.Prover.mutually_recursive_functions_whose_ensures_contradict_each_other
        [ "prover.termination"; "prover.termination" ]);
  Harness.test "a recursive call in a requires is compared with the entry measure" (fun () ->
      expect_not_proven Fixtures.Prover.recursive_function_whose_requires_calls_itself
        "prover.termination");
  Harness.test
    "the contract of a function bound as a value is assumed only for arguments that meet their \
     invariants" (fun () ->
      expect_not_proven Fixtures.Prover.function_value_whose_ensures_needs_its_parameters_invariant
        "prover.ensures");
  Harness.test
    "the ensures of a function passed as an argument is assumed only for arguments that meet their \
     invariants" (fun () ->
      expect_not_proven
        Fixtures.Prover.function_argument_whose_ensures_needs_its_parameters_invariant
        "prover.ensures");
  Harness.test
    "a generic type's invariant that calls an impl is an error where the impl uses the type"
    (fun () ->
      expect_circular_at_each
        Fixtures.Prover.invariant_of_a_generic_type_calling_the_impl_that_uses_it
        ~says:
          [
            "A value of type `Box[Marker]` is used here, and the invariant of that type or of a \
             part of it depends on `Marker.measure`, so the invariant would be proven from itself.";
            "The invariant of that type or of a part of it depends on `Marker.measure`, whose \
             proof depends on `held`";
          ]);
  Harness.test
    "a generic type that holds itself with its type arguments swapped depends on the impls of both \
     arguments" (fun () ->
      expect_circular_at_each Fixtures.Prover.generic_type_holding_itself_with_swapped_arguments
        ~says:
          [
            "A value of type `Alternating[Marker, Ruler]` is used here, and the invariant of that \
             type or of a part of it depends on `Marker.measure`";
            "A value of type `Alternating[Ruler, Marker]` is used here. The invariant of that type \
             or of a part of it depends on `Marker.measure`, whose proof depends on `held`";
          ]);
  Harness.test
    "a method of an impl may use a generic type whose invariant calls another method of the impl"
    (fun () ->
      expect_proven Fixtures.Prover.generic_type_whose_invariant_calls_another_method_of_the_impl)

let list_evaluated_definitions text =
  let database = Support.make_database (Support.setup [ ("app.main", text) ]) in
  List.map
    (fun item -> Option.fold ~none:"" ~some:Path.show (Lowered.Item.find_definition item))
    (Database.list_evaluations (Support.prove database (Support.parse_file "app.main")))

let expect_proven_trusting_compiled_code text ~code ~count =
  let database = Support.make_database (Support.setup [ ("app.main", text) ]) in
  let states =
    List.filter
      (fun (state : Database.proof_state) -> state.site.code = code)
      (Support.list_proof_states database (Support.parse_file "app.main"))
  in
  if List.length states <> count then Harness.fail "%d %s states" (List.length states) code;
  List.iter
    (fun (state : Database.proof_state) ->
      if (not state.is_proven) || not state.trusts_compiled_code then
        Harness.fail "a %s state is not proven by an evaluation" code)
    states

let unfinished_constant = "fn build() -> UInt64 {\n  todo\n}\n\nlet unfinished: UInt64 = build()\n"

let () =
  Harness.test "the proofs of a file ask for each constant whose value calls a function" (fun () ->
      match list_evaluated_definitions Fixtures.Prover.computed_constants with
      | [ "app.main.corner"; "app.main.day_is_even"; "app.main.seconds_per_day"; "app.main.shape" ]
        ->
          ()
      | evaluated -> Harness.fail "evaluates [%s]" (String.concat "; " evaluated));
  Harness.test "code that reads a computed constant knows its value, and trusts compiled code"
    (fun () ->
      expect_proven_trusting_compiled_code Fixtures.Prover.computed_constants ~code:"prover.ensures"
        ~count:6);
  Harness.test "a proof that needs the value of an unfinished constant says that it has none"
    (fun () ->
      Support.expect_one_diagnostic ~check
        (unfinished_constant ^ "\nfn f() -> UInt64\n  ensures result == 4\n{\n  unfinished\n}\n")
        "prover.ensures"
        ~says:
          "The evaluation of `app.main.unfinished` stopped, so its value is not known: todo reached");
  Harness.test "a constant computed from an unfinished constant is unfinished, and no error"
    (fun () ->
      expect_proven
        (unfinished_constant
       ^ "\n\
          fn double(value: UInt64) -> UInt64 {\n\
         \  value.saturating_add(value)\n\
          }\n\n\
          let twice: UInt64 = double(unfinished)\n"));
  Harness.test
    "a constant computed from a cyclic constant is unfinished: only the cycle is an error, and a \
     proof that needs the value says that it has none" (fun () ->
      match
        List.sort compare
          (List.map
             (fun (diagnostic : Diagnostic.t) ->
               (Diagnostic.Code.name diagnostic.code, diagnostic.message))
             (list_diagnostics
                (Fixtures.Prover.constant_computed_from_a_cyclic_constant
               ^ "\nfn f() -> UInt64\n  ensures result == 4\n{\n  twice\n}\n")))
      with
      | [ ("prover.constant_cycle", _); ("prover.ensures", message) ] ->
          if
            not
              (String.includes
                 ~affix:
                   "The evaluation of `app.main.twice` stopped, so its value is not known: the \
                    value of `app.main.limit` depends on itself"
                 message)
          then Harness.fail "%s" message
      | diagnostics ->
          Harness.fail "[%s]" (String.concat "; " (List.map (fun (code, _) -> code) diagnostics)));
  Harness.test "a member constant's value is proven and evaluated as a constant's is" (fun () ->
      match List.sort compare (list_codes Fixtures.Prover.member_constants_computed_by_calls) with
      | [ "prover.constant_cycle"; "prover.requires" ] -> ()
      | codes -> Harness.fail "codes [%s]" (String.concat "; " codes));
  Harness.test "a constant for specifications only is not evaluated" (fun () ->
      match
        list_evaluated_definitions
          "fn twice(value: Integer) -> Integer {\n\
          \  value * 2\n\
           }\n\n\
           let big: Integer = twice(1_000_000_000_000_000_000_000)\n\n\
           fn f(value: Int64) -> Int64\n\
          \  requires value < big\n\
           {\n\
          \  value\n\
           }\n"
      with
      | [] -> ()
      | evaluated -> Harness.fail "evaluates [%s]" (String.concat "; " evaluated))

let () =
  let accepted = Fixtures.Prover.accepted_values in
  let assert_then condition result =
    Printf.sprintf "fn f() -> UInt64 {\n  proof {\n    assert %s by evaluation\n  }\n  %s\n}\n"
      condition result
  in
  Harness.test "an assertion by evaluation that holds proves its fact, and trusts compiled code"
    (fun () ->
      let text = accepted ^ assert_then "is_accepted(97)" "accept(97)" in
      expect_proven text;
      expect_proven_trusting_compiled_code text ~code:"prover.assertion" ~count:1);
  Harness.test "an assertion by evaluation that is false fails every time" (fun () ->
      Support.expect_one_diagnostic ~check
        (accepted ^ assert_then "is_accepted(98)" "98")
        "prover.assertion"
        ~says:"`is_accepted(98)` may not hold. This fails every time the code reaches it."
        ~at:("is_accepted(98)", 1));
  Harness.test "a call in the condition of an assertion by evaluation meets its requires" (fun () ->
      expect_not_proven (accepted ^ assert_then "accept(5) == 5" "5") "prover.requires");
  Harness.test "an assertion by evaluation that reaches a todo says where" (fun () ->
      Support.expect_one_diagnostic ~check
        ("fn unfinished() -> Bool {\n  todo\n}\n\n" ^ assert_then "unfinished()" "1")
        "prover.assertion" ~says:"Its evaluation stopped, so its result is not known: todo reached");
  Harness.test "a function cannot assert its own result by evaluation" (fun () ->
      expect_codes
        "fn lies() -> Bool\n\
        \  ensures result\n\
         {\n\
        \  proof {\n\
        \    assert lies() by evaluation\n\
        \  }\n\
        \  false\n\
         }\n"
        [ "prover.ensures"; "prover.termination" ]);
  Harness.test "a constant cannot be asserted by evaluation in the function that computes it"
    (fun () ->
      expect_codes
        "fn count() -> Int64\n\
        \  ensures result > 0\n\
         {\n\
        \  proof {\n\
        \    assert counted > 0 by evaluation\n\
        \  }\n\
        \  0\n\
         }\n\n\
         let counted: Int64 = count()\n"
        [ "prover.constant_cycle"; "prover.ensures" ]);
  Harness.test "an assertion by evaluation is proven in each place where an assertion is written"
    (fun () ->
      expect_proven Fixtures.Prover.assertions_by_evaluation_in_each_place;
      match list_evaluated_definitions Fixtures.Prover.assertions_by_evaluation_in_each_place with
      | [ _; _; _; _; _; _ ] -> ()
      | evaluated -> Harness.fail "evaluates [%s]" (String.concat "; " evaluated))

let () =
  Harness.test "a loop with an invariant" (fun () ->
      expect_proven Fixtures.Prover.loop_with_an_invariant);
  Harness.test "a loop invariant that an iteration breaks" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_breaking_its_invariant "prover.invariant");
  Harness.test "a while loop's default measure holds in a function that terminates" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_toward_a_bound_it_does_not_approach
        "prover.termination");
  Harness.test "a while loop's default measure is not checked where the function may run forever"
    (fun () ->
      expect_proven
        Fixtures.Prover.while_loop_toward_a_bound_it_does_not_approach_where_it_may_run_forever);
  Harness.test "a loop's written measure holds where the function may run forever" (fun () ->
      expect_not_proven
        Fixtures.Prover.while_loop_whose_measure_does_not_decrease_where_it_may_run_forever
        "prover.termination");
  Harness.test "a while loop whose condition begins with a comparison is measured by its distance"
    (fun () ->
      expect_proven Fixtures.Prover.while_loop_measured_by_the_comparison_that_begins_its_condition);
  Harness.test "the comparison that begins a condition measures a loop that must terminate"
    (fun () ->
      expect_not_proven
        Fixtures.Prover.while_loop_toward_the_bound_of_the_comparison_that_begins_its_condition
        "prover.termination");
  Harness.test "a loop invariant must hold on entry to the loop" (fun () ->
      expect_not_proven ~says:"may not hold on entry to the loop"
        Fixtures.Prover.invariant_broken_on_entry "prover.invariant"
        ~fixed:
          ("fn f(limit: Int64) -> Int64 {", "fn f(limit: Int64) -> Int64\n  requires 0 <= limit\n{");
      expect_not_proven ~says:"may not hold on entry to the loop"
        Fixtures.Prover.range_loop_invariant_broken_on_entry "prover.invariant";
      expect_not_proven ~says:"may not hold on entry to the loop"
        Fixtures.Prover.list_loop_invariant_broken_on_entry "prover.invariant");
  Harness.test "a loop invariant must be well defined at every iteration, not only on entry"
    (fun () ->
      expect_not_proven Fixtures.Prover.invariant_reading_past_the_last_element
        "prover.out_of_bounds");
  Harness.test "a loop that a `break` leaves knows the facts of its path, not its invariant"
    (fun () ->
      expect_proven Fixtures.Prover.break_below_the_invariant;
      expect_not_proven Fixtures.Prover.break_below_the_invariant_ensured_at_or_above_zero
        "prover.ensures");
  Harness.test "an iteration that a `continue` ends must decrease the loop's measure" (fun () ->
      expect_not_proven Fixtures.Prover.continue_before_the_step "prover.termination");
  Harness.test "an iteration that a `continue` ends must keep the loop's invariant" (fun () ->
      expect_proven Fixtures.Prover.continue_after_the_step;
      expect_not_proven Fixtures.Prover.continue_breaking_the_invariant "prover.invariant";
      expect_not_proven Fixtures.Prover.continue_breaking_the_invariant_of_a_list_loop
        "prover.invariant");
  Harness.test "`old` in a loop invariant is the value on entry to the function, not to the loop"
    (fun () ->
      expect_proven Fixtures.Prover.old_in_an_invariant_after_a_change;
      expect_not_proven ~says:"may not hold on entry to the loop"
        Fixtures.Prover.old_in_an_invariant_read_as_the_loop_entry "prover.invariant");
  Harness.test "a loop's measures are compared lexicographically" (fun () ->
      expect_proven Fixtures.Prover.loop_measure_refilling_its_second_component;
      expect_not_proven Fixtures.Prover.loop_measure_whose_first_component_grows
        "prover.termination");
  Harness.test "a loop's measure must be well defined" (fun () ->
      expect_not_proven Fixtures.Prover.loop_measure_reading_an_element "prover.out_of_bounds");
  Harness.test "a loop's cost clause is defined after each iteration" (fun () ->
      expect_not_proven Fixtures.Prover.loop_cost_clause_dividing_by_a_local_that_the_body_zeroes
        "prover.division");
  Harness.test "a measure on a loop over a range or a list is compared at each iteration" (fun () ->
      expect_proven Fixtures.Prover.measures_of_loops_over_a_range_and_a_list;
      expect_not_proven Fixtures.Prover.range_loop_measure_that_stays_the_same "prover.termination");
  Harness.test "an impl of FiniteCursor whose next does not decrease remaining is rejected"
    (fun () ->
      expect_not_proven Fixtures.Prover.finite_cursor_whose_next_does_not_decrease_remaining
        "prover.ensures");
  Harness.test "a restated clause is proven of the receiver that the method changes" (fun () ->
      expect_not_proven Fixtures.Prover.restated_clause_that_the_changed_receiver_breaks
        "prover.ensures");
  Harness.test "an impl of FiniteCursor proves the decrease from its next's ensures" (fun () ->
      expect_proven Fixtures.Prover.finite_cursor_kept_by_its_next);
  Harness.test "a loop over a type parameter bound by FiniteCursor ends" (fun () ->
      expect_proven Fixtures.Prover.loop_over_a_bound_finite_cursor);
  Harness.test "an omitted argument has its trait's default on a known type and through a bound"
    (fun () ->
      expect_proven Fixtures.Prover.default_of_a_trait_method_read_through_a_bound;
      expect_not_proven Fixtures.Prover.default_of_a_trait_method_ensured_as_another_value
        "prover.ensures");
  Harness.test "a caller spends the allocations of a default that it applies" (fun () ->
      expect_proven Fixtures.Prover.allocations_of_a_default_that_the_caller_applies;
      expect_not_proven Fixtures.Prover.allocations_of_a_default_left_out_of_the_callers_cost
        "prover.cost");
  Harness.test "a construction spends the allocations of a field default that it applies" (fun () ->
      expect_proven Fixtures.Prover.allocations_of_a_field_default_that_the_construct_applies;
      expect_not_proven
        Fixtures.Prover.allocations_of_a_field_default_left_out_of_the_constructs_cost "prover.cost");
  Harness.test "a call through a bound has the clauses that the bound's trait restates" (fun () ->
      expect_proven Fixtures.Prover.restated_clause_through_a_bound);
  Harness.test "a call that names the restating trait has the restated clauses" (fun () ->
      expect_proven Fixtures.Prover.restated_method_called_through_its_trait);
  Harness.test "a loop over a take of a list ends through FiniteCursor's restated next" (fun () ->
      expect_proven Fixtures.Prover.loop_over_a_take_of_a_list);
  Harness.test "an impl whose method's cost exceeds the restated cost is rejected" (fun () ->
      expect_not_proven Fixtures.Prover.restated_cost_that_the_contract_breaks "prover.cost");
  Harness.test "an impl whose method's cost meets the restated cost is proven" (fun () ->
      expect_proven Fixtures.Prover.restated_cost_that_the_contract_keeps);
  Harness.test "a clause with a condition is proven with the condition's bounds" (fun () ->
      expect_proven Fixtures.Infer.clause_calling_a_method_of_its_condition;
      expect_not_proven Fixtures.Prover.conditional_ensures_broken "prover.ensures");
  Harness.test "a call has the clause whose condition its type arguments meet" (fun () ->
      expect_proven Fixtures.Prover.conditional_ensures_at_a_call_that_meets_it;
      expect_not_proven Fixtures.Prover.conditional_ensures_at_a_call_that_does_not_meet_it
        "prover.ensures");
  Harness.test "a loop's measure with a condition is proven where the condition holds" (fun () ->
      expect_not_proven Fixtures.Prover.conditional_measure_that_does_not_decrease
        "prover.termination");
  Harness.test "a loop's cost with a condition counts the loop only where the condition holds"
    (fun () ->
      expect_proven Fixtures.Prover.conditional_loop_cost_kept;
      Support.expect_one_diagnostic ~check Fixtures.Prover.conditional_loop_cost_broken
        "prover.cost" ~says:"may not hold after an iteration.");
  Harness.test "a condition's run reads a bound's associated type as its constraint" (fun () ->
      expect_proven Fixtures.Prover.conditional_measure_of_a_cursor_with_a_constrained_element);
  Harness.test "a requires that a call leaves undecided is proven with its condition" (fun () ->
      Support.expect_one_diagnostic ~check
        Fixtures.Prover.conditional_requires_left_undecided_at_a_call "prover.requires"
        ~fixed:
          ( "uses Items.Uses\n{\n  first(mut items)",
            "uses Items.Uses\n\
            \  requires items.remaining() > 0 when Items: FiniteCursor\n\
             {\n\
            \  first(mut items)" )
        ~says:"`source.remaining() > 0` may not hold for this call to `first`.");
  Harness.test "a recursion measured under a condition ends where the condition holds" (fun () ->
      expect_proven Fixtures.Prover.recursion_measured_under_a_condition;
      expect_not_proven Fixtures.Prover.recursion_that_does_not_end_under_its_condition
        "prover.termination");
  Harness.test "an adapter's loop ends where its capability set's condition holds" (fun () ->
      expect_proven Fixtures.Capabilities.adapter_whose_capability_set_has_a_condition;
      expect_not_proven Fixtures.Prover.adapter_whose_measure_does_not_decrease_under_its_condition
        "prover.termination");
  Harness.test "a measure whose condition a supertrait gives is proven under the subtrait"
    (fun () -> expect_proven Fixtures.Prover.measure_proven_under_a_subtrait);
  Harness.test "a caller without `Panic` proves a callee's condition on values" (fun () ->
      expect_proven Fixtures.Prover.scaled_under_a_condition_on_its_argument;
      Support.expect_one_diagnostic ~check Fixtures.Prover.scaled_without_a_proof_of_its_condition
        "prover.panic" ~at:("scaled(value)", 1)
        ~fixed:
          ( "requires value >= 0\n{\n  scaled(value)",
            "requires value >= 0\n  requires value * 1000 <= Int64.maximum\n{\n  scaled(value)" )
        ~alternatives:[ ("requires value >= 0", "uses Panic\n  requires value >= 0") ]);
  Harness.test "a function rules out every panic where its condition on values holds" (fun () ->
      expect_not_proven Fixtures.Prover.crash_where_the_condition_holds "prover.panic";
      expect_proven Fixtures.Prover.crash_where_the_condition_fails;
      expect_not_proven Fixtures.Prover.operation_that_fails_where_the_condition_holds
        "prover.overflow"
        ~fixed:
          ( "uses Panic unless count < 200\n{\n  count + 100",
            "uses Panic unless count < 200\n\
            \  requires count <= UInt8.maximum - 100\n\
             {\n\
            \  count + 100" ));
  Harness.test "a caller that panics unless a condition proves its callee's where it holds"
    (fun () ->
      match list_codes Fixtures.Prover.condition_passed_on_to_a_callee with
      | [ "prover.panic" ] -> ()
      | codes -> Harness.fail "%s" (String.concat ", " codes));
  Harness.test "a specification proves the condition of a function it calls" (fun () ->
      expect_proven Fixtures.Prover.function_with_a_condition_on_values_in_a_specification;
      expect_not_proven
        Fixtures.Prover.function_with_a_condition_on_values_in_a_specification_outside_it
        "prover.panic"
        ~fixed:
          ( "ensures text.byte(0) == 48 ==> result\n{\n  text.byte(0) == 48",
            "ensures text.byte(0) == 48 ==> result\n\
            \  requires 0 < text.length()\n\
             {\n\
            \  text.byte(0) == 48" ));
  Harness.test "expect needs no `Panic` where its value is proven present" (fun () ->
      expect_proven Fixtures.Prover.expect_of_a_value_proven_present;
      expect_not_proven Fixtures.Prover.expect_of_a_value_that_may_be_absent "prover.panic"
        ~fixed:
          ( "fn first(values: List[Int64]) -> Int64 {",
            "fn first(values: List[Int64]) -> Int64\n  uses Panic\n{" ));
  Harness.test "an impl's condition on values follows from its trait's" (fun () ->
      Support.expect_one_diagnostic ~check Fixtures.Prover.impl_condition_beyond_its_trait
        "prover.requires" ~says:"may not follow from the trait's condition after `Panic unless`";
      expect_proven Fixtures.Prover.impl_condition_within_its_trait);
  Harness.test "a call through a bound without `Panic` proves the trait's condition on values"
    (fun () ->
      Support.expect_one_diagnostic ~check
        Fixtures.Prover.call_through_a_bound_beyond_the_trait_condition "prover.panic"
        ~fixed:
          ( "fn large[Shape: Sized](shape: Shape) -> Int64 {",
            "fn large[Shape: Sized](shape: Shape) -> Int64\n  uses Panic\n{" )
        ~says:"may not hold for this call to `Sized.size`, so the call may panic");
  Harness.test "a loop that counts up to its bound ends" (fun () ->
      expect_proven Fixtures.Prover.while_loop_counting_up);
  Harness.test "a for loop over a range knows its index is in range" (fun () ->
      expect_proven Fixtures.Prover.range_index_plus_one);
  Harness.test "recursion that decreases" (fun () ->
      expect_proven Fixtures.Prover.recursion_that_decreases);
  Harness.test "recursion that does not decrease" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_that_does_not_decrease "prover.termination");
  Harness.test "a function's written measure holds where it may run forever" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_that_does_not_decrease_where_it_may_run_forever
        "prover.termination");
  Harness.test "recursion without a measure is not checked where the function may run forever"
    (fun () -> expect_proven Fixtures.Prover.recursion_without_a_measure_where_it_may_run_forever);
  Harness.test "a function's measures are compared lexicographically" (fun () ->
      expect_proven Fixtures.Prover.ackermann;
      expect_not_proven Fixtures.Prover.measure_whose_second_component_grows "prover.termination");
  Harness.test "a measure must be bounded below by zero" (fun () ->
      expect_proven Fixtures.Prover.recursion_and_loop_on_a_measure_kept_at_zero;
      expect_codes Fixtures.Prover.recursion_on_a_measure_below_zero [ "prover.termination" ];
      expect_not_proven Fixtures.Prover.loop_measure_below_zero "prover.termination");
  Harness.test "a requires fix leaves out a comparison that holds for every value" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_on_a_measure_below_zero "prover.termination"
        ~fixed:("  decreases steps\n{", "  decreases steps\n  requires 0 <= steps\n{"));
  Harness.test "a recursive call in a quantifier's body decreases within the quantifier's range"
    (fun () ->
      expect_proven Fixtures.Prover.recursion_in_a_quantifier_over_smaller_values;
      expect_not_proven Fixtures.Prover.recursion_in_a_quantifier_reaching_its_own_value
        "prover.termination");
  Harness.test "a recursive call decreases from the measure on entry, before `self` changes"
    (fun () ->
      expect_proven Fixtures.Prover.counter_drained_through_mut_self;
      expect_not_proven Fixtures.Prover.counter_refilled_through_mut_self "prover.termination");
  Harness.test "a function's measure must be well defined" (fun () ->
      expect_proven Fixtures.Prover.measure_dividing_by_a_required_divisor;
      expect_not_proven Fixtures.Prover.measure_dividing_by_a_parameter "prover.division"
        ~fixed:
          ( "  decreases count, 100 / divisor\n{",
            "  decreases count, 100 / divisor\n  requires divisor != 0\n{" ));
  Harness.test "a contract that calls its own function applies the function's limited copy"
    (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Prover.recursive_total_in_its_own_contract) ]
      in
      let caller = List.hd (Support.list_declarations packages (Support.parse_module "app.main")) in
      let rec applies_limited (term : Logic.term) =
        match term with
        | Apply (Limited _, _) -> true
        | Apply (_, terms) | Operation (_, terms) -> List.exists applies_limited terms
        | Is (_, term) | Exists (_, term) -> applies_limited term
        | Forall (_, triggers, body) -> List.exists applies_limited (body :: triggers)
        | Symbol _ | Integer _ | Boolean _ | Bits _ -> false
      in
      match
        Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main")
          caller.key
      with
      | Obligations { obligations = [ obligation ]; _ } ->
          if not (List.exists applies_limited obligation.query.facts) then
            Harness.fail "no fact applies the limited copy: %s" (Logic.show_query obligation.query)
      | _ -> Harness.fail "expected one obligation")

let () =
  Harness.test "mutual recursion without measures cannot be shown to end" (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Prover.even_and_odd_without_measures) ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "prover.termination"; "prover.termination" ] -> ()
      | codes -> Harness.fail "codes %s" (String.concat ", " codes));
  Harness.test "mutual recursion that decreases" (fun () ->
      expect_proven Fixtures.Prover.even_and_odd_with_measures);
  Harness.test "functions in a cycle compare the common prefix of their measures lexicographically"
    (fun () ->
      expect_proven Fixtures.Prover.cycle_with_measures_of_two_lengths;
      expect_not_proven Fixtures.Prover.cycle_with_measures_tied_on_their_common_prefix
        "prover.termination");
  Harness.test "an impl that reaches itself through a generic function cannot be shown to end"
    (fun () ->
      expect_codes Fixtures.Prover.check_reaching_itself_through_a_generic [ "prover.termination" ])

let () =
  List.iter
    (fun (failure, broken) ->
      Harness.test
        ("a proof that reads a contract with " ^ failure ^ " is blocked and reports nothing")
        (fun () ->
          let packages =
            Support.setup
              [ ("app.main", Fixtures.Prover.caller_of_double); ("app.main/broken", broken) ]
          in
          let main = Support.parse_file "app.main" in
          (match
             Support.list_codes
               (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers
                  (Support.make_database packages) main)
           with
          | [] -> ()
          | codes -> Harness.fail "the caller does not check: %s" (String.concat ", " codes));
          (match
             Support.list_codes
               (Support.list_proof_diagnostics (Support.make_database packages) main)
           with
          | [] -> ()
          | codes -> Harness.fail "the blocked proof reports %s" (String.concat ", " codes));
          let caller =
            List.find
              (fun (declaration : Resolve.Names.declaration) ->
                Path.equal declaration.key.path (Support.make_top_path "app.main" "caller"))
              (Support.list_declarations packages (Support.parse_module "app.main"))
          in
          match
            Database.For_testing.find_proof
              (Support.prove (Support.make_database packages) main)
              caller.key
          with
          | Some Blocked -> ()
          | Some (Value _ | Failed) -> Harness.fail "the proof is computed"
          | None -> Harness.fail "the caller has no proof"))
    [
      ("a type error", Fixtures.Prover.double_with_an_ill_typed_ensures);
      ("a match that misses a case", Fixtures.Prover.double_with_an_ensures_that_misses_a_case);
    ]

let () =
  Harness.test "a proof blocked by an error in a package its package depends on is not a bug"
    (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib.numbers", Fixtures.Prover.public_double_with_an_ill_typed_ensures);
            ("app.main", Fixtures.Prover.caller_of_a_dependency_with_an_ill_typed_ensures);
          ]
      in
      let main = Support.parse_file "app.main" in
      (match
         Support.list_codes
           (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers
              (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller does not check: %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.key.path (Support.make_top_path "app.main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app.main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          caller.key
      with
      | Some Blocked -> ()
      | Some (Value _ | Failed) -> Harness.fail "the proof is computed"
      | None -> Harness.fail "the caller has no proof");
  Harness.test "a function that passes a derived impl where a bound needs one is proven" (fun () ->
      expect_not_proven Fixtures.Prover.same_of_a_derived_version_ensured_false "prover.ensures");
  Harness.test
    "a written default that calls a function that calls a derived default is not recursion"
    (fun () ->
      expect_proven Fixtures.Prover.person_default_over_a_function_calling_a_derived_default)

let () =
  Harness.test "a type error in a callee's body blocks no caller's proof" (fun () ->
      let packages =
        Support.setup
          [
            ("app.main", Fixtures.Prover.caller_of_double);
            ("app.main/double", Fixtures.Prover.double_with_an_ill_typed_body);
          ]
      in
      let main = Support.parse_file "app.main" in
      (match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller's proof reports %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.key.path (Support.make_top_path "app.main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app.main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          caller.key
      with
      | Some (Value (Obligations _)) -> ()
      | Some (Value (Unsupported _ | Not_proven_here)) ->
          Harness.fail "the caller has no obligations"
      | Some (Failed | Blocked) -> Harness.fail "the proof is blocked"
      | None -> Harness.fail "the caller has no proof");
  Harness.test "a body that calls a broken signature blocks no caller's proof" (fun () ->
      let packages =
        Support.setup
          [
            ("app.main", Fixtures.Prover.caller_of_double);
            ("app.main/double", Fixtures.Prover.double_reading_a_secret);
          ]
      in
      let main = Support.parse_file "app.main" in
      (match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller's proof reports %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.key.path (Support.make_top_path "app.main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app.main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          caller.key
      with
      | Some (Value (Obligations _)) -> ()
      | Some (Value (Unsupported _ | Not_proven_here)) ->
          Harness.fail "the caller has no obligations"
      | Some (Failed | Blocked) -> Harness.fail "the proof is blocked"
      | None -> Harness.fail "the caller has no proof")

let () =
  Harness.test "a broken method of a trait blocks no call of its other methods" (fun () ->
      let packages =
        Support.setup
          [
            ("app.main", Fixtures.Prover.total_of_a_box_size);
            ("app.main/measured", Fixtures.Prover.measured_trait_with_a_broken_method);
          ]
      in
      let database = Support.make_database packages in
      let main = Support.parse_file "app.main" in
      (match
         Support.list_codes
           (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database
              (Support.parse_file "app.main/measured"))
       with
      | [ "resolve.unknown_name" ] -> ()
      | codes -> Harness.fail "the trait reports %s" (String.concat ", " codes));
      (match
         Support.list_codes
           (Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers database
              main)
       with
      | [] -> ()
      | codes -> Harness.fail "a caller does not check: %s" (String.concat ", " codes));
      (match Support.list_codes (Support.list_proof_diagnostics database main) with
      | [] -> ()
      | codes -> Harness.fail "a caller's proof reports %s" (String.concat ", " codes));
      let proofs = Support.prove database main in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match Database.For_testing.find_proof proofs declaration.key with
          | Some (Value (Obligations _)) -> ()
          | Some (Value (Unsupported _ | Not_proven_here)) ->
              Harness.fail "%s has no obligations" (Path.show declaration.key.path)
          | Some (Failed | Blocked) ->
              Harness.fail "the proof of %s is blocked" (Path.show declaration.key.path)
          | None -> Harness.fail "%s has no proof" (Path.show declaration.key.path))
        ((Support.make_names packages).list_declarations_in main))

let tree = Fixtures.Prover.tree

let () =
  Harness.test "recursion on a part of a parameter ends" (fun () ->
      expect_proven (tree ^ Fixtures.Prover.leftmost));
  Harness.test "recursion on the parameter itself does not end" (fun () ->
      expect_not_proven (tree ^ Fixtures.Prover.spin_on_its_tree) "prover.termination");
  Harness.test "recursion on a part of the first parameter ends while a second one grows" (fun () ->
      expect_proven Fixtures.Prover.chain_reversed_onto_a_growing_chain);
  Harness.test "recursion on a part of a parameter ends while a later one is unchanged" (fun () ->
      expect_proven Fixtures.Prover.chain_searched_beside_an_unchanged_chain);
  Harness.test "recursion on a part of a parameter ends while an earlier one is unchanged"
    (fun () -> expect_proven Fixtures.Prover.chain_searched_after_an_unchanged_chain);
  Harness.test "recursion on a part of a parameter does not end while an earlier one grows"
    (fun () ->
      expect_not_proven
        ~says:
          "This recursive call may not be on a part of the first of `grown` and `chain` that it \
           changes: give the function a `decreases` clause."
        Fixtures.Prover.chain_counted_while_the_first_chain_grows "prover.termination");
  Harness.test "a user's model is not known to be smaller than its value" (fun () ->
      expect_not_proven Fixtures.Prover.spin_on_a_knot_whose_model_holds_it "prover.termination");
  Harness.test "a match with guards ends in an unreachable that is proven" (fun () ->
      expect_proven Fixtures.Prover.match_with_exhaustive_guards;
      expect_not_proven Fixtures.Prover.match_with_guards_missing_zero "prover.unreachable")

let () =
  Harness.test "a theorem the solver proves alone" (fun () ->
      expect_proven Fixtures.Prover.squares_grow);
  Harness.test "a quantifier over a range" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_an_inclusive_range "prover.ensures");
  Harness.test "an `exists` is proven by an element that meets it" (fun () ->
      expect_proven Fixtures.Prover.exists_from_a_witness;
      expect_not_proven Fixtures.Prover.exists_without_a_witness "prover.ensures");
  Harness.test "an `exists` does not prove a `forall`" (fun () ->
      expect_not_proven Fixtures.Prover.exists_read_as_forall "prover.ensures");
  Harness.test "an `Integer` passed for a `UInt64` must fit, given the operands of `&&` before it"
    (fun () ->
      expect_proven Fixtures.Prover.integer_guarded_before_it_is_passed_as_a_uint64;
      expect_codes Fixtures.Prover.integer_passed_where_a_uint64_is_expected
        [ "prover.out_of_range"; "prover.out_of_range" ]);
  Harness.test "a callee's ensures is not known where its requires fails" (fun () ->
      expect_not_proven Fixtures.Prover.ensures_of_a_callee_outside_its_requires "prover.ensures");
  Harness.test "an assert in a test is a fact, not an obligation" (fun () ->
      expect_proven Fixtures.Prover.test_asserting_a_false_equality);
  Harness.test "an assert in a theorem is an obligation" (fun () ->
      expect_not_proven Fixtures.Prover.theorem_asserting_a_positive_parameter "prover.assertion")

let shape = Fixtures.Prover.shape
let point = "type Point(x: Int64, y: Int64)\n  derives Equal\n\n"

let () =
  Harness.test "match binds a variant's fields" (fun () ->
      expect_proven (shape ^ Fixtures.Prover.match_on_a_shape));
  Harness.test "a variant's field is in its type's range, and no further" (fun () ->
      expect_not_proven
        (shape ^ Fixtures.Prover.circle_radius_squared)
        "prover.overflow"
        ~fixed:("fn f(shape: Shape) -> Int64 {", "fn f(shape: Shape) -> Int64\n  uses Panic\n{"));
  Harness.test "a requires fix states a negated comparison as the opposite comparison" (fun () ->
      expect_not_proven
        (point ^ Fixtures.Prover.point_kept_off_a_corner)
        "prover.ensures"
        ~fixed:
          ( "  ensures point.x != 5 || point.y != 6\n{",
            "  ensures point.x != 5 || point.y != 6\n  requires point.x != 5 || point.y != 6\n{" );
      expect_not_proven Fixtures.Prover.increment_unless_a_flag "prover.overflow"
        ~fixed:
          ( "fn f(flag: Bool, count: UInt8) -> UInt8 {",
            "fn f(flag: Bool, count: UInt8) -> UInt8\n\
            \  requires (!flag) ==> (count <= UInt8.maximum - 1)\n\
             {" )
        ~alternatives:
          [
            ( "fn f(flag: Bool, count: UInt8) -> UInt8 {",
              "fn f(flag: Bool, count: UInt8) -> UInt8\n  uses Panic\n{" );
          ]);
  Harness.test "a requires can match on a parameter" (fun () ->
      expect_proven (shape ^ Fixtures.Prover.requires_matching_a_shape));
  Harness.test "with replaces one field and keeps the others" (fun () ->
      expect_proven (point ^ Fixtures.Prover.point_with_x_incremented));
  Harness.test "derived equality is the solver's equality" (fun () ->
      expect_proven (point ^ Fixtures.Prover.point_rebuilt_equals_itself));
  Harness.test "is binds the parts it matches, where it is true" (fun () ->
      expect_proven Fixtures.Prover.is_some_positive);
  Harness.test "? continues with the value inside" (fun () ->
      expect_not_proven Fixtures.Prover.question_mark_on_an_option "prover.overflow"
        ~fixed:
          ( "fn f(value: Option[UInt8]) -> Option[UInt8] {",
            "fn f(value: Option[UInt8]) -> Option[UInt8]\n  uses Panic\n{" ));
  Harness.test "? returns an error unchanged" (fun () ->
      expect_proven Fixtures.Prover.question_mark_on_a_result)

let () =
  Harness.test "an index must be in bounds" (fun () ->
      expect_not_proven Fixtures.Prover.index_without_a_bound "prover.out_of_bounds");
  Harness.test "an index the requires bounds" (fun () ->
      expect_proven Fixtures.Prover.index_bounded_by_the_requires);
  Harness.test "an index a range loop bounds" (fun () ->
      expect_proven Fixtures.Prover.saturating_sum_over_a_range);
  Harness.test "assigning to an element checks its index" (fun () ->
      expect_not_proven Fixtures.Prover.element_assigned_without_a_bound "prover.out_of_bounds");
  Harness.test "a function's ensures is what its callers know" (fun () ->
      expect_proven Fixtures.Prover.is_small_known_by_its_ensures);
  Harness.test "an impl method's contract is read at a call" (fun () ->
      expect_proven Fixtures.Prover.counter_next_through_its_contract);
  Harness.test "a mut argument that is a field leaves the rest of its value as it was" (fun () ->
      expect_proven Fixtures.Prover.point_field_bumped);
  Harness.test "a mut argument that is a field is known only by the callee's postcondition"
    (fun () -> expect_not_proven Fixtures.Prover.point_field_reset "prover.ensures");
  Harness.test "assigning a field keeps the other fields" (fun () ->
      expect_proven Fixtures.Prover.point_field_assigned)

let measured = Fixtures.Prover.measured

let () =
  Harness.test "an impl's method must keep its trait's ensures" (fun () ->
      expect_not_proven (measured ^ Fixtures.Prover.box_measure_of_its_size) "prover.ensures");
  Harness.test "an impl's method that keeps its trait's ensures" (fun () ->
      expect_proven (measured ^ Fixtures.Prover.box_measure_clamped_at_zero));
  Harness.test "an impl's requires may not be stronger than its trait's" (fun () ->
      expect_not_proven
        (measured ^ Fixtures.Prover.box_measure_with_a_stronger_requires)
        "prover.requires");
  Harness.test "a call through a bound knows its trait's ensures, not an impl's stronger one"
    (fun () ->
      let text = measured ^ Fixtures.Prover.box_measure_ensured_at_least_ten in
      expect_not_proven text "prover.ensures" ~at:("shape.measure()", 1))

let each_index = Fixtures.Prover.each_index

let () =
  Harness.test "a lambda's body is proven where it is written" (fun () ->
      expect_not_proven Fixtures.Prover.apply_of_an_overflowing_lambda "prover.overflow");
  Harness.test "a lambda may rely on its callee's promise about its arguments" (fun () ->
      expect_proven (each_index ^ Fixtures.Prover.each_index_reading_items));
  Harness.test "a lambda without such a promise knows nothing of its arguments" (fun () ->
      expect_not_proven Fixtures.Prover.each_without_a_promise "prover.out_of_bounds");
  Harness.test "a function must keep its promise to its callback" (fun () ->
      expect_not_proven Fixtures.Prover.each_index_visiting_count "prover.requires");
  Harness.test "a function that keeps its promise to its callback" (fun () ->
      expect_proven Fixtures.Prover.each_index_visiting_below_count)

let () =
  Harness.test "a push's contract, through the list's model" (fun () ->
      expect_proven Fixtures.Prover.push_of_five);
  Harness.test "a push does not keep the length" (fun () ->
      expect_not_proven Fixtures.Prover.push_ensured_to_keep_the_length "prover.ensures");
  Harness.test "an index into a list after a push is in bounds" (fun () ->
      expect_proven Fixtures.Prover.index_after_a_push);
  Harness.test "identical is the same value, for any type" (fun () ->
      expect_proven Fixtures.Prover.identical_of_a_value_and_itself)

let () =
  Harness.test "a loop over a list runs once per element" (fun () ->
      expect_proven Fixtures.Prover.list_loop_counted);
  Harness.test "a loop's element is the list's element at its position" (fun () ->
      expect_proven Fixtures.Prover.list_loop_checking_each_positive);
  Harness.test "a loop over a list does not run once more" (fun () ->
      expect_not_proven Fixtures.Prover.list_loop_counted_one_too_many "prover.ensures");
  Harness.test "a loop over the elements of a constant is proven" (fun () ->
      expect_proven Fixtures.Prover.loop_over_constant_primes)

let couple = Fixtures.Prover.couple

let () =
  Harness.test "a lending method keeps its contract on each path that lends" (fun () ->
      expect_proven couple);
  let make_tagged_source ensures =
    Fixtures.Prover.pair_tagged_signature ^ ensures
    ^ "{\n  Tagged(tag: 0, value: mut self.second)\n}\n"
  in
  Harness.test "a constructor lent `mut` does not mutate a field of `self` that it does not lend"
    (fun () -> expect_proven (make_tagged_source "  ensures self.first == old(self.first)\n"));
  Harness.test "a caller's mutation of a constructor lent `mut` is written to the lent field"
    (fun () ->
      expect_not_proven
        (make_tagged_source "  ensures self.second == old(self.second)\n")
        "prover.ensures");
  Harness.test "a caller of a method that lends a constructor `mut` can rely on its `ensures`"
    (fun () ->
      expect_proven
        (make_tagged_source "  ensures self.first == old(self.first)\n"
        ^ Fixtures.Prover.pair_first_kept_through_a_lent_constructor));
  Harness.test "a caller's mutation of a part lent `mut` is its `final(result)`" (fun () ->
      expect_proven Fixtures.Prover.cell_part_lent_mut);
  Harness.test
    "a part lent `mut` to a `match` is written back before an arm that binds no name assigns the \
     lender" (fun () ->
      expect_proven Fixtures.Prover.cell_assigned_by_an_arm_after_lending_its_part_mut);
  let raised_before_lending = Fixtures.Prover.counter_raised_before_its_count_is_lent in
  Harness.test "a caller assumes a clause on the lent part in the state where the method lends"
    (fun () -> expect_not_proven raised_before_lending "prover.ensures" ~at:("seen", 2));
  Harness.test "a clause on the lent part that names the entry state tells a caller the part"
    (fun () ->
      expect_proven
        (List.fold_left Support.apply_edit raised_before_lending
           [
             ("ensures result == self.count", "ensures result == old(self.count) + 1");
             ("ensures result == 3", "ensures result == 4");
           ]));
  Harness.test "a clause that names `final(result)` holds when the lend ends and may name `result`"
    (fun () -> expect_proven Fixtures.Prover.counter_slot_naming_the_lent_and_the_final_part);
  let slotted = Fixtures.Prover.counter_implementing_a_lending_trait_method in
  Harness.test
    "an impl of a lending trait method proves the trait's `ensures`, and a caller through a bound \
     assumes them" (fun () ->
      expect_proven
        (slotted
       ^ "\n\
          fn raise[Holder: Slotted](holder: mut Holder)\n\
         \  ensures holder.count() == 4\n\
          {\n\
         \  mut holder.slot() = 4\n\
          }\n"));
  Harness.test "a trait's clause on the lent part is checked where the impl lends" (fun () ->
      let kept = "ensures result == old(self.count())" in
      expect_not_proven
        (Support.apply_edit slotted (kept, kept ^ " + 1"))
        "prover.ensures" ~at:("self.count\n  }\n}", 1)
        ~says:"The trait's `result == old(self.count()) + 1` may not hold for the part lent here.");
  Harness.test "a trait's clause on `final(result)` is checked when the impl's lend ends" (fun () ->
      let kept = "ensures self.count() == final(result)" in
      expect_not_proven
        (Support.apply_edit slotted (kept, kept ^ " + 1"))
        "prover.ensures"
        ~says:
          "The trait's `self.count() == final(result) + 1` may not hold when the method ends here.");
  Harness.test "a method that lends `mut` a part with an invariant assumes the caller left it valid"
    (fun () -> expect_proven Fixtures.Prover.holder_lending_a_part_with_an_invariant);
  Harness.test
    "a proof reads a receiver whose part is lent `mut` as the method left it where it lent"
    (fun () -> expect_proven Fixtures.Prover.deque_read_while_its_element_is_lent);
  let lent_while_counting = Fixtures.Prover.part_lent_while_another_argument_changes in
  Harness.test "the end of a lend changes the lender and no other `mut` argument" (fun () ->
      expect_proven lent_while_counting;
      expect_not_proven
        (Support.apply_edit lent_while_counting ("ensures result == 6", "ensures result == 1"))
        "prover.ensures");
  Harness.test
    "a restated clause of a lending method is proven where it lends and when its lend ends"
    (fun () ->
      let restated = Fixtures.Prover.restated_lending_clause_that_the_contract_does_not_give in
      let given = "    ensures result == old(self.count)\n" in
      expect_not_proven restated "prover.ensures" ~says:"`self.count() == final(result)`";
      expect_proven
        (Support.apply_edit restated (given, given ^ "    ensures self.count == final(result)\n")));
  Harness.test "a lending method that lends a part it does not promise" (fun () ->
      expect_not_proven Fixtures.Prover.couple_larger_lending_first "prover.ensures"
        ~fixed:
          ( "ensures result >= self.first && result >= self.second\n{\n  self.first",
            "ensures result >= self.first && result >= self.second\n\
            \  requires self.first >= self.second\n\
             {\n\
            \  self.first" ));
  Harness.test "a loop over a user's collection gets the facts of its `count` and its `element`"
    (fun () -> expect_proven (couple ^ Fixtures.Prover.couple_loop_counted));
  Harness.test
    "the elements that a loop has read meet the postcondition of the collection's `element`"
    (fun () -> expect_proven (couple ^ Fixtures.Prover.couple_loop_with_known_elements));
  Harness.test "a loop over a user's collection has visited the collection's model when it ends"
    (fun () -> expect_proven Fixtures.Prover.couple_with_a_model_totaled_by_a_loop);
  Harness.test "the elements that a loop has read are not known beyond that postcondition"
    (fun () ->
      expect_not_proven
        (couple ^ Fixtures.Prover.couple_loop_with_one_known_element)
        "prover.invariant");
  Harness.test "an `IterableMut` impl's `element` must keep the collection's count" (fun () ->
      expect_not_proven Fixtures.Prover.row_loop_changing_counts "prover.ensures");
  Harness.test "a loop over a range has visited its indexes" (fun () ->
      expect_proven Fixtures.Prover.range_loop_counted_by_visited);
  Harness.test "a range loop's index in its clauses is the next index" (fun () ->
      expect_proven Fixtures.Prover.range_loop_counted_by_its_index);
  Harness.test "a range loop's index counts from the range's start" (fun () ->
      expect_proven Fixtures.Prover.range_loop_from_a_start);
  Harness.test "a range loop's index in its clauses is past the last index at the end" (fun () ->
      expect_not_proven Fixtures.Prover.range_loop_with_an_index_invariant "prover.invariant");
  Harness.test "an inclusive range loop's index in its clauses runs through one past its end"
    (fun () -> expect_proven Fixtures.Prover.inclusive_range_loop_counting);
  Harness.test "a range loop's index bounds its cost" (fun () ->
      expect_proven Fixtures.Prover.range_loop_with_an_index_cost_clause);
  Harness.test "a loop over a type's own cursor calls its next" (fun () ->
      expect_proven Fixtures.Prover.countdown_loop);
  Harness.test "a loop over a cursor in a field calls its next and keeps the other fields"
    (fun () -> expect_proven Fixtures.Prover.countdown_in_a_field);
  (let scanner =
     "type Scanner(length: UInt64, position: UInt64, count: UInt64)\n\
      fn advance(scanner: mut Scanner)\n\
     \  modifies scanner.position\n\
     \  requires scanner.position < 1000\n\
     \  ensures scanner.position == old(scanner.position) + 1\n\
      {\n\
     \  scanner.position += 1\n\
      }\n"
   in
   Harness.test "a call keeps the parts that its callee's modifies clause does not name" (fun () ->
       expect_proven
         (scanner
        ^ "fn step(scanner: mut Scanner)\n\
          \  requires scanner.position < 1000\n\
          \  ensures scanner.length == old(scanner.length) && scanner.count == old(scanner.count)\n\
           {\n\
          \  advance(mut scanner)\n\
           }\n");
       expect_not_proven
         (scanner
        ^ "fn step(scanner: mut Scanner)\n\
          \  requires scanner.position < 1000\n\
          \  ensures scanner.position == old(scanner.position)\n\
           {\n\
          \  advance(mut scanner)\n\
           }\n")
         "prover.ensures");
   Harness.test "a modifies entry that the body never changes leaves the proof to run" (fun () ->
       let packages =
         Support.setup [ ("app.main", Fixtures.Prover.increment_under_an_unchanged_modifies_entry) ]
       in
       let file = Support.parse_file "app.main" in
       (match Support.list_codes (check packages file) with
       | [ "usage.unmodified_part" ] -> ()
       | codes -> Harness.fail "checking: %s" (String.concat ", " codes));
       match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) file)
       with
       | [ "prover.overflow" ] -> ()
       | codes -> Harness.fail "proving: %s" (String.concat ", " codes));
   Harness.test "a loop keeps the parts that its body and its callees do not change" (fun () ->
       let loop ~body =
         scanner
         ^ "fn walk(scanner: mut Scanner)\n\
           \  requires scanner.position <= scanner.length && scanner.length < 1000\n\
           \  ensures scanner.length == old(scanner.length) && scanner.count == old(scanner.count)\n\
            {\n\
           \  while scanner.position < scanner.length\n\
           \    invariant scanner.position <= scanner.length\n\
           \    decreases scanner.length - scanner.position\n\
           \  {\n" ^ body ^ "\n  }\n}\n"
       in
       expect_proven (loop ~body:"    scanner.position += 1");
       expect_proven (loop ~body:"    advance(mut scanner)");
       expect_not_proven
         (loop ~body:"    scanner.position += 1\n    scanner.count += 0")
         "prover.ensures"));
  Harness.test "a loop over a cursor counts a body that calls an amortized callee" (fun () ->
      expect_proven Fixtures.Prover.spaced_characters);
  (let samples = Fixtures.Prover.samples in
   Harness.test "an assignment through an index is to a key the collection accepts" (fun () ->
       expect_proven (samples ^ Fixtures.Prover.samples_stored_within_bounds));
   Harness.test "an assignment through an index to a key the collection does not accept" (fun () ->
       expect_not_proven
         (samples ^ Fixtures.Prover.samples_stored_without_a_bound)
         "prover.requires"
         ~fixed:
           ( "fn store(samples: mut Samples, position: UInt64) {",
             "fn store(samples: mut Samples, position: UInt64)\n\
             \  requires position < samples.values.length()\n\
              {" )));
  Harness.test "a later arm sees an earlier arm's guard's mutations" (fun () ->
      expect_proven Fixtures.Prover.match_guard_bumping_a_count);
  Harness.test "assigning an element mutates only that element" (fun () ->
      expect_proven Fixtures.Prover.first_element_assigned_zero);
  Harness.test "a compound assignment to an element" (fun () ->
      expect_proven Fixtures.Prover.compound_assignment_to_an_element);
  let digit = Fixtures.Prover.digit in
  Harness.test "an assignment evaluates its value, then its target's index keys" (fun () ->
      expect_proven (digit ^ Fixtures.Prover.assignment_order_ensured_value_first);
      expect_not_proven
        (digit ^ Fixtures.Prover.assignment_order_ensured_index_first)
        "prover.ensures");
  Harness.test "a compound assignment evaluates its operand, then its target's index keys, once"
    (fun () ->
      expect_proven (digit ^ Fixtures.Prover.compound_assignment_order_ensured_once);
      expect_not_proven
        (digit ^ Fixtures.Prover.compound_assignment_order_ensured_twice)
        "prover.ensures")

let monoid = Fixtures.Prover.monoid

let make_flag_impl_source empty =
  Printf.sprintf
    "impl Monoid for Flag {\n\
    \  fn empty() -> Flag\n\
    \    ensures result == Flag(on: %s)\n\
    \  {\n\
    \    Flag(on: %s)\n\
    \  }\n\n\
    \  fn combine(self, other: Flag) -> Flag\n\
    \    ensures result == Flag(on: self.on || other.on)\n\
    \  {\n\
    \    Flag(on: self.on || other.on)\n\
    \  }\n\
     }\n"
    empty empty

let () =
  Harness.test "an impl's methods keep its trait's law" (fun () ->
      expect_proven (monoid ^ make_flag_impl_source "false"));
  Harness.test "an impl whose methods break its trait's law" (fun () ->
      expect_not_proven (monoid ^ make_flag_impl_source "true") "prover.law");
  Harness.test "generic code relies on a bound's laws" (fun () ->
      expect_proven (monoid ^ make_flag_impl_source "false" ^ Fixtures.Prover.monoid_identity));
  Harness.test "a law holds on every path after its first use" (fun () ->
      expect_proven Fixtures.Prover.choice_law_on_every_path)

let () =
  Harness.test "an impl's method keeps its trait's time clause, so a law reads its ensures"
    (fun () -> expect_proven (monoid ^ Fixtures.Prover.int64_monoid))

let () =
  Harness.test "wrapping arithmetic is a remainder" (fun () ->
      expect_proven Fixtures.Prover.wrapping_arithmetic_identities);
  Harness.test "wrapping subtraction wraps below zero" (fun () ->
      expect_proven Fixtures.Prover.wrapping_subtraction_from_one);
  Harness.test "saturating addition stops at the bound" (fun () ->
      expect_proven Fixtures.Prover.saturating_add_of_the_maximum);
  Harness.test "saturating addition is exact where it fits" (fun () ->
      expect_proven Fixtures.Prover.saturating_add_that_fits);
  Harness.test "a checked addition is none exactly when it overflows" (fun () ->
      expect_proven Fixtures.Prover.checked_add_of_255);
  Harness.test "a conversion succeeds exactly when the value fits" (fun () ->
      expect_proven Fixtures.Prover.try_from_of_an_int64);
  Harness.test "a widening conversion needs no check of its range" (fun () ->
      expect_proven Fixtures.Prover.integer_widened_without_a_check);
  Harness.test "a float conversion keeps the value of a float or an integer" (fun () ->
      expect_proven Fixtures.Prover.float_conversions_keep_the_value);
  Harness.test "a widening conversion keeps the value" (fun () ->
      expect_proven Fixtures.Prover.to_index);
  Harness.test "a widening conversion costs constant time" (fun () ->
      expect_proven Fixtures.Prover.widen);
  Harness.test "a widening conversion keeps a range from a type's invariant" (fun () ->
      expect_proven Fixtures.Prover.digit_index);
  Harness.test "unwrap_or gives the held value or the default" (fun () ->
      expect_proven Fixtures.Prover.digit_unwrap_or);
  Harness.test "wrapping is not exact arithmetic" (fun () ->
      expect_not_proven Fixtures.Prover.wrapping_add_ensured_larger "prover.ensures")

let span = "type Span(low: Int64, high: Int64)\n  invariant low <= high\n\n"

let () =
  (let counter = ("app.counter", Fixtures.Prover.counter_with_a_private_invariant) in
   Harness.test
     "another module assumes and passes on an invariant clause that names a private definition"
     (fun () ->
       Support.expect_no_diagnostics ~check
         [ ("app.main", Fixtures.Prover.counter_passed_through_another_module); counter ]);
   Harness.test "another module does not know an invariant clause that names a private definition"
     (fun () ->
       Support.expect_one_diagnostic ~check ~others:[ counter ]
         Fixtures.Prover.counter_read_by_another_module "prover.ensures"
         ~fixed:
           ( "ensures result <= 10\n{\n  value.count",
             "ensures result <= 10\n  requires value.count <= 10\n{\n  value.count" ));
   Harness.test "another module cannot prove an invariant clause that names a private definition"
     (fun () ->
       Support.expect_one_diagnostic ~check ~others:[ counter ]
         Fixtures.Prover.counter_built_by_another_module "prover.invariant"));
  Harness.test "building a value must meet its invariant" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_built_without_its_invariant)
        "prover.invariant"
        ~fixed:("fn f(low: Int64) -> Span {", "fn f(low: Int64) -> Span\n  requires low <= 0\n{"));
  Harness.test "building a value that meets its invariant" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_built_within_its_invariant));
  Harness.test "a derived Default must meet the invariant" (fun () ->
      expect_not_proven Fixtures.Prover.positive_default "prover.invariant");
  Harness.test "a derived Default's failure points at its `derives` entry" (fun () ->
      let text = Fixtures.Prover.positive_default in
      match list_diagnostics text with
      | [ { span; _ } ] when String.sub text span.start (span.stop - span.start) = "Default" -> ()
      | actual -> Harness.fail "%s" (String.concat "; " (Support.list_codes actual)));
  Harness.test "a derived Default built from field defaults meets the invariant" (fun () ->
      expect_proven Fixtures.Prover.positive_default_from_field_defaults);
  Harness.test "a field's default must meet its type's invariant" (fun () ->
      expect_not_proven Fixtures.Prover.holder_defaulting_to_an_invalid_positive "prover.invariant");
  Harness.test "a parameter meets its invariant" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_parameter_ensured_ordered));
  Harness.test "a mut parameter must meet its invariant at the return that ends the function"
    (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_high_assigned_below_low)
        "prover.invariant" ~at:("range.high = range.low - 1", 1));
  Harness.test "a body may break an invariant between calls" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_low_assigned_above_high));
  Harness.test "a var must meet its invariant when its scope ends" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_var_assigned_past_its_invariant)
        "prover.invariant";
      expect_not_proven
        (span ^ Fixtures.Prover.span_var_in_a_loop_body_past_its_invariant)
        "prover.invariant");
  Harness.test "a with must meet the invariant" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_updated_past_its_invariant)
        "prover.invariant"
        ~fixed:
          ("fn f(span: Span) -> Int64 {", "fn f(span: Span) -> Int64\n  requires 10 <= span.high\n{");
      expect_proven (span ^ Fixtures.Prover.span_updated_within_its_invariant));
  Harness.test "a with through a path must meet the invariant of the record it rebuilds" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.interval_updated_past_its_span_invariant)
        "prover.invariant"
        ~fixed:
          ( "fn f(interval: Interval) -> Int64 {",
            "fn f(interval: Interval) -> Int64\n  requires 10 <= interval.span.high\n{" ));
  Harness.test "a var may break its invariant before its scope ends" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_var_restored_before_its_scope_ends));
  Harness.test "a var changed through a field passed mut must meet its invariant" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_var_field_passed_mut_past_its_invariant)
        "prover.invariant");
  Harness.test "a var that a step of an update leaves broken must meet its invariant" (fun () ->
      expect_not_proven (span ^ Fixtures.Prover.span_var_left_broken_by_a_step) "prover.invariant");
  Harness.test "a value passed to a call must meet its invariant" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_passed_after_breaking_its_invariant)
        "prover.invariant");
  Harness.test "a private method that takes mut self is a step of an update" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_restore));
  Harness.test "a step of an update assumes the invariants of its fields" (fun () ->
      expect_proven (span ^ Fixtures.Prover.step_passing_a_field_that_meets_its_invariant));
  Harness.test "a step of an update leaves its fields meeting their invariants" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.step_leaving_a_field_past_its_invariant)
        "prover.invariant");
  Harness.test "a public method that takes mut self is not a step of an update" (fun () ->
      expect_not_proven (span ^ Fixtures.Prover.span_restored_by_a_public_method) "prover.invariant");
  Harness.test "a method of a private trait that takes mut self is not a step of an update"
    (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_restored_by_a_method_of_a_private_trait)
        "prover.invariant")

let run = Fixtures.Prover.run

let () =
  Harness.test "a named function that keeps its parameter type's cost" (fun () ->
      expect_proven (run ^ Fixtures.Prover.same_as_a_constant_time_value));
  Harness.test "a named function must accept every argument its parameter's type promises"
    (fun () ->
      expect_not_proven Fixtures.Prover.apply_of_a_visit_requiring_below_five "prover.requires");
  Harness.test "a named function that accepts every argument its parameter's type promises"
    (fun () -> expect_proven Fixtures.Prover.apply_of_a_visit_requiring_below_ten);
  Harness.test "naming a function that reaches back is recursion that cannot be shown to end"
    (fun () -> expect_not_proven (run ^ Fixtures.Prover.again_running_itself) "prover.termination")

let () =
  Harness.test "a list literal has its elements in order" (fun () ->
      expect_proven Fixtures.Prover.list_literal_element_read);
  Harness.test "a list literal has its length" (fun () ->
      expect_proven Fixtures.Prover.list_literal_length);
  Harness.test "an array literal has its elements" (fun () ->
      expect_proven Fixtures.Prover.array_literal_element_read);
  Harness.test "an index below an array's count is within it" (fun () ->
      expect_proven Fixtures.Prover.array_index_below_its_count);
  Harness.test "an index at an array's count is not" (fun () ->
      expect_not_proven Fixtures.Prover.array_index_at_its_count "prover.out_of_bounds");
  Harness.test "a non-empty list literal is one allocation" (fun () ->
      expect_proven Fixtures.Prover.list_literal_with_one_allocation);
  Harness.test "a string literal copied for its owner is one allocation" (fun () ->
      expect_proven Fixtures.Prover.string_literal_returned_with_one_allocation);
  Harness.test "a string literal copied for its owner is not free" (fun () ->
      expect_not_proven Fixtures.Prover.string_literal_returned_with_no_allocations "prover.cost");
  Harness.test "an empty string literal allocates nothing" (fun () ->
      expect_proven Fixtures.Prover.empty_string_with_no_allocations);
  Harness.test "reading a string literal allocates nothing" (fun () ->
      expect_proven Fixtures.Prover.string_literal_read_with_no_allocations);
  Harness.test "a copy has its original's capacity" (fun () ->
      expect_proven Fixtures.Prover.capacity_of_a_copy);
  Harness.test "sequences with the same elements are identical" (fun () ->
      expect_proven Fixtures.Prover.first_element_rewritten);
  Harness.test "sequences that differ in one element are not identical" (fun () ->
      expect_not_proven Fixtures.Prover.first_element_changed "prover.ensures")

let () =
  Harness.test "a value or itself is itself, bit for bit" (fun () ->
      expect_proven Fixtures.Prover.or_with_itself);
  Harness.test "a value xor itself is zero" (fun () ->
      expect_proven Fixtures.Prover.xor_with_itself);
  Harness.test "signed bitwise operations are two's complement" (fun () ->
      expect_proven Fixtures.Prover.signed_bitwise_assertion);
  Harness.test "a shift by a literal is a multiplication" (fun () ->
      expect_proven Fixtures.Prover.shift_by_four_of_a_small_byte);
  Harness.test "a bit-vector assertion holds for every value of its variables" (fun () ->
      expect_not_proven Fixtures.Prover.bit_vector_assertion_without_its_hypothesis
        "prover.assertion");
  Harness.test "a bit-vector assertion states its hypotheses" (fun () ->
      expect_proven Fixtures.Prover.bit_vector_assertion_with_its_hypothesis);
  Harness.test "a bitwise fact that does not hold is not proven" (fun () ->
      expect_not_proven Fixtures.Prover.low_bit_ensured_zero "prover.ensures")

let () =
  Harness.test "a range's elements are its collection's, from its start" (fun () ->
      expect_proven Fixtures.Prover.range_element_read);
  Harness.test "a list passed read-only is a view with its model" (fun () ->
      expect_proven Fixtures.Prover.count_of_a_list_as_a_range);
  Harness.test "two views of one list are one value, so a function of them agrees" (fun () ->
      expect_proven Fixtures.Prover.short_list_passed_where_a_short_range_is_required);
  Harness.test "two views of one string are one value, so a function of them agrees" (fun () ->
      expect_proven Fixtures.Prover.short_text_passed_where_a_short_range_is_required);
  Harness.test "a range must be within its collection" (fun () ->
      expect_not_proven Fixtures.Prover.range_past_the_end "prover.out_of_bounds");
  Harness.test "two ranges lent together must not overlap" (fun () ->
      expect_not_proven Fixtures.Prover.both_of_overlapping_ranges "prover.disjoint");
  Harness.test "a range copied into from an overlapping range of one list" (fun () ->
      expect_not_proven Fixtures.Prover.range_copied_from_an_overlapping_range "prover.disjoint");
  Harness.test "an element bound to `_` is still proven in bounds" (fun () ->
      expect_not_proven Fixtures.Prover.element_out_of_bounds_bound_to_a_wildcard
        "prover.out_of_bounds");
  Harness.test "a `mut` list parameter whose elements alone change keeps its length through a call"
    (fun () -> expect_proven Fixtures.Prover.range_parameter_keeps_its_length_through_a_call);
  Harness.test "two halves of a list can be lent together" (fun () ->
      expect_proven Fixtures.Prover.both_halves_of_a_list)

let () =
  Harness.test "a string literal's length is its bytes'" (fun () ->
      expect_proven Fixtures.Prover.length_of_a_string_with_an_accent);
  Harness.test "a long string literal has its length without a fact for each byte" (fun () ->
      expect_proven Fixtures.Prover.length_of_a_long_string_literal);
  Harness.test "a string's length plus one, a sum of two, and the room below the maximum fit"
    (fun () -> expect_proven Fixtures.Prover.sums_of_lengths_that_fit);
  Harness.test "a sum of three string lengths may overflow" (fun () ->
      expect_not_proven Fixtures.Prover.sum_of_three_lengths "prover.overflow"
        ~fixed:
          ( "fn f(first: String, second: String, third: String) -> UInt64 {",
            "fn f(first: String, second: String, third: String) -> UInt64\n  uses Panic\n{" ));
  Harness.test "pushing text onto a string adds its length" (fun () ->
      expect_proven Fixtures.Prover.string_push);
  Harness.test "a string pattern matches text with its bytes" (fun () ->
      expect_proven Fixtures.Prover.match_on_string_patterns);
  Harness.test "an interpolated string is a string about which little is known" (fun () ->
      expect_not_proven Fixtures.Prover.length_of_an_interpolated_string "prover.ensures")

let shout = Fixtures.Prover.shout

let () =
  Harness.test "a tagged template meets its tag's requires" (fun () ->
      expect_proven (shout ^ Fixtures.Prover.shout_of_a_literal));
  Harness.test "a call of from_template through a bound must meet the tag's check" (fun () ->
      expect_not_proven Fixtures.Prover.from_template_through_a_bound "prover.requires"
        ~fixed:
          ( "fn make[Made: FromTemplate](template: Template[Made.Interpolation]) -> Made {",
            "fn make[Made: FromTemplate](template: Template[Made.Interpolation]) -> Made\n\
            \  requires Made.is_valid_template(template.literals)\n\
             {" ));
  Harness.test "a call of from_template through a bound meets the check its caller requires"
    (fun () -> expect_proven Fixtures.Prover.from_template_through_a_bound_that_requires_the_check);
  Harness.test "a tagged template whose check gives false fails every time it is reached" (fun () ->
      let message = read_message (shout ^ Fixtures.Prover.shout_of_a_copied_name) in
      if
        not
          (String.includes
             ~affix:
               "The call to `Shout.is_valid_template` that `Shout\"hey ${name.copy()}\"` makes may \
                not give `true`. This fails every time the code reaches it."
             message)
      then Harness.fail "message %S" message);
  Harness.test "a proof knows the length and the text of a template's literals with no evaluation"
    (fun () ->
      let tag = Fixtures.Prover.generic_tag_whose_check_states_its_result in
      let of_any_tone ?(parameters = "") template =
        Printf.sprintf "fn of_any_tone[Tone](%s) -> Shout[Tone] {\n  %s\n}\n" parameters template
      in
      (match list_evaluated_definitions (tag ^ of_any_tone "Shout\"hey\"") with
      | [] -> ()
      | evaluated -> Harness.fail "evaluates [%s]" (String.concat "; " evaluated));
      expect_proven (tag ^ of_any_tone "Shout\"hey\"");
      expect_not_proven
        (tag ^ of_any_tone ~parameters:"name: String" "Shout\"hey ${name.copy()}\"")
        "prover.requires";
      expect_not_proven (tag ^ of_any_tone "Shout\"hello\"") "prover.requires");
  Harness.test "a template copies its literal text once, as a string literal is copied" (fun () ->
      let count = Fixtures.Prover.template_counting_its_literals in
      let of_count clause = Printf.sprintf "fn f() -> Count\n  %s\n{\n  Count\"hey\"\n}\n" clause in
      expect_proven (count ^ of_count "cost allocations == 1");
      expect_not_proven (count ^ of_count "cost allocations == 0") "prover.cost");
  Harness.test "a generic tag at a type without type parameters is checked by evaluation" (fun () ->
      (match list_evaluated_definitions Fixtures.Prover.generic_tag_without_a_stated_check with
      | [ "app.main.loud" ] -> ()
      | evaluated -> Harness.fail "evaluates [%s]" (String.concat "; " evaluated));
      expect_proven Fixtures.Prover.generic_tag_without_a_stated_check);
  Harness.test "an impl's from_template cannot require more than the tag's check" (fun () ->
      expect_not_proven Fixtures.Prover.shout_with_a_stronger_requires "prover.requires");
  let fails_every_time = "This fails every time the code reaches it." in
  let breaking_return = Fixtures.Prover.early_return_breaking_its_ensures in
  Harness.test "an obligation that fails whenever its path is taken is refuted" (fun () ->
      expect_not_proven breaking_return "prover.ensures" ~says:fails_every_time ~at:("return 8", 1));
  Harness.test "an obligation that holds on some runs of its path is not refuted" (fun () ->
      let message =
        read_message (Support.apply_edit breaking_return ("return 8", "return number"))
      in
      if String.includes ~affix:fails_every_time message then Harness.fail "message %S" message);
  Harness.test "an obligation that the solver cannot decide is refuted where its path refutes it"
    (fun () ->
      expect_not_proven Fixtures.Prover.early_return_breaking_its_ensures_after_a_call
        "prover.ensures" ~says:fails_every_time);
  Harness.test "an ensures that one branch of a final `if` breaks is refuted at that branch's value"
    (fun () ->
      expect_not_proven Fixtures.Prover.final_if_breaking_its_ensures_in_one_branch "prover.ensures"
        ~says:fails_every_time ~at:("8", 1));
  Harness.test "an ensures that one arm of a final `match` breaks is refuted at that arm's value"
    (fun () ->
      expect_not_proven Fixtures.Prover.final_match_breaking_its_ensures_in_one_arm "prover.ensures"
        ~says:fails_every_time ~at:("8", 1));
  Harness.test
    "an ensures on a `mut` parameter that one branch of a final `if` breaks is refuted at that \
     branch's end" (fun () ->
      expect_not_proven Fixtures.Prover.final_if_breaking_a_mut_parameters_ensures_in_one_branch
        "prover.ensures" ~says:fails_every_time ~at:("value = -1", 1));
  Harness.test "an obligation that the facts refute says it fails every time it is reached"
    (fun () ->
      let message = read_message Fixtures.Prover.element_past_the_end_of_a_literal in
      if not (String.includes ~affix:"This fails every time the code reaches it." message) then
        Harness.fail "message %S" message)

let () =
  Harness.test "float equality is reflexive, even for NaN" (fun () ->
      expect_proven Fixtures.Prover.float_equal_to_itself);
  Harness.test "every float is ordered, NaN last" (fun () ->
      expect_proven Fixtures.Prover.float_at_most_itself);
  Harness.test "float arithmetic is exact where IEEE 754 is" (fun () ->
      expect_proven Fixtures.Prover.quarter_plus_quarter);
  Harness.test "adding zero keeps a float equal, with -0.0 equal to 0.0" (fun () ->
      expect_proven Fixtures.Prover.float_plus_zero_compared_with_itself);
  Harness.test "adding one does not always make a float larger" (fun () ->
      expect_not_proven Fixtures.Prover.float_plus_one_ensured_larger "prover.ensures");
  Harness.test "a derived equality over floats compares field by field" (fun () ->
      expect_proven Fixtures.Prover.float_point_equality);
  Harness.test "equal points have equal fields" (fun () ->
      expect_proven Fixtures.Prover.float_points_compared_by_field);
  Harness.test "points equal by their fields are not identical" (fun () ->
      expect_not_proven Fixtures.Prover.float_points_equal_and_identical "prover.ensures")

let dice = Fixtures.Prover.dice

let () =
  let choosing = Fixtures.Prover.capability_method_taking_a_callback in
  Harness.test
    "a lambda passed to a capability method assumes its parameter's `requires` and meets its \
     `ensures`" (fun () -> expect_proven choosing);
  Harness.test "a lambda passed to a capability method must meet its parameter's `ensures`"
    (fun () ->
      expect_not_proven
        (Support.apply_edit choosing ("100 / n % n", "n.saturating_add(1)"))
        "prover.ensures");
  Harness.test "a trait method called through two instances of its trait is two functions"
    (fun () ->
      expect_not_proven Fixtures.Prover.trait_method_called_through_two_instances_of_its_trait
        "prover.ensures");
  Harness.test "a trait method called at two result types is two functions" (fun () ->
      expect_not_proven Fixtures.Prover.trait_method_called_at_two_result_types "prover.ensures");
  Harness.test "a recursive call at another instance is not compared by its parts" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_at_another_instance "prover.termination");
  let counting = Fixtures.Prover.loop_over_characters_across_the_surrogates in
  Harness.test "a loop over a range of characters visits no surrogate" (fun () ->
      expect_proven counting;
      expect_not_proven
        (Support.apply_edit counting ("result == 2", "result == 2050"))
        "prover.ensures");
  let quantified = Fixtures.Prover.quantifier_over_characters_across_the_surrogates in
  Harness.test "a quantifier over a range of characters ranges over no surrogate" (fun () ->
      expect_proven quantified;
      expect_not_proven (Support.apply_edit quantified ("  false\n", "  true\n")) "prover.ensures");
  let promising = Fixtures.Prover.lambda_promising_the_ensures_of_an_earlier_lambda in
  Harness.test "a lambda meets a parameter's `ensures` that names an earlier lambda" (fun () ->
      expect_proven promising;
      expect_not_proven
        (Support.apply_edit promising ("fn(y) { y })", "fn(y) { y / 2 })"))
        "prover.ensures");
  let generic = Fixtures.Prover.generic_function_passed_for_a_parameter_with_a_contract in
  Harness.test "a generic function passed as a value is read at its type arguments" (fun () ->
      expect_proven generic;
      expect_not_proven
        (Support.apply_edit generic
           ("-> UInt64 ensures result == items.length()))", "-> UInt64 ensures result == 0))"))
        "prover.ensures");
  Harness.test "a function named as a value in its own ensures is read once" (fun () ->
      expect_codes Fixtures.Prover.function_named_as_a_value_in_its_own_ensures
        [ "prover.circular_proof" ]);
  let kept = Fixtures.Prover.named_function_passed_for_a_type_parameter in
  Harness.test "a named function passed for a type parameter meets its requires for every argument"
    (fun () ->
      expect_proven kept;
      expect_not_proven
        (Support.apply_edit kept ("-> UInt8\n{", "-> UInt8\n  requires n % 2 == 0\n{"))
        "prover.requires");
  let inherited = Fixtures.Prover.impl_ensures_proven_under_the_trait_requires in
  Harness.test "an impl's ensures hold where the trait's requires do, which its proof assumed"
    (fun () ->
      expect_proven inherited;
      expect_codes
        (Support.apply_edit inherited
           ( "  requires x > 0\n  ensures result == Eager().tag(x)",
             "  requires x > 0 ==> Eager().tag(x) == Eager().tag(x)\n  ensures result > 0" ))
        [ "prover.ensures" ]);
  let held = Fixtures.Prover.named_function_held_in_a_local_then_passed in
  Harness.test "a function value keeps its contract where a local holds it" (fun () ->
      expect_proven held;
      expect_codes
        (Support.apply_edit held ("  ensures result == 1\n{\n  1", "  ensures result <= 1\n{\n  1"))
        [ "prover.ensures" ]);
  Harness.test "a callback chosen by a condition is known as neither choice" (fun () ->
      expect_codes Fixtures.Prover.callback_chosen_by_a_condition [ "prover.ensures" ]);
  Harness.test "a callback with a requires that a condition chooses accepts every argument"
    (fun () ->
      expect_codes Fixtures.Prover.callback_with_a_requires_chosen_by_a_condition
        [ "prover.requires" ]);
  Harness.test "a quantifier over a type ranges over values whose fields are in range" (fun () ->
      expect_codes Fixtures.Prover.quantifier_over_a_type_with_a_ranged_field [ "prover.ensures" ]);
  let nested = Fixtures.Prover.generic_impl_contract_read_at_a_nested_type in
  Harness.test "a generic impl's ensures are read inside their own at a smaller type" (fun () ->
      expect_proven nested;
      expect_not_proven
        (Support.apply_edit nested ("ensures result == 3", "ensures result == 4"))
        "prover.ensures");
  Harness.test "a restated clause holds of the trait arguments that its trait requires" (fun () ->
      expect_codes Fixtures.Prover.restated_clause_of_another_trait_argument [ "prover.ensures" ]);
  Harness.test "a call in a quantifier over no value gives no fact outside the quantifier"
    (fun () ->
      expect_codes Fixtures.Prover.recursive_call_in_a_quantifier_over_no_value [ "prover.ensures" ]);
  Harness.test "two calls of a function that may panic give one result for one argument" (fun () ->
      expect_proven Fixtures.Prover.function_that_may_panic_called_twice);
  let costed = Fixtures.Prover.two_lambdas_with_one_value_and_two_costs in
  Harness.test "two lambdas with one value and two costs are costed apart" (fun () ->
      expect_proven costed;
      expect_codes
        (Support.apply_edit costed
           ("    let _ = item\n  })\n}", "    let _ = [item, item]\n  })\n}"))
        [ "prover.cost" ]);
  Harness.test "the contract of a function that can panic is assumed only where it returns"
    (fun () ->
      expect_codes Fixtures.Prover.contract_of_a_function_that_panics_assumed_where_it_panics
        [ "prover.overflow" ]);
  Harness.test "a capability's method keeps its ensures" (fun () ->
      expect_proven (dice ^ Fixtures.Prover.dice_roll_ensured_at_most_six));
  Harness.test "two calls of a capability's method may differ" (fun () ->
      expect_not_proven (dice ^ Fixtures.Prover.two_dice_rolls_compared) "prover.ensures");
  Harness.test "a call must meet a capability method's requires" (fun () ->
      expect_not_proven Fixtures.Prover.store_put_of_an_unchecked_slot "prover.requires")

let () =
  Harness.test "a set contains its inserted elements" (fun () ->
      expect_proven Fixtures.Prover.set_insert_then_contains);
  Harness.test "inserting an element a set contains leaves it unchanged" (fun () ->
      expect_proven Fixtures.Prover.insert_into_a_set_that_contains_it);
  Harness.test "inserting into a set may mutate it" (fun () ->
      expect_not_proven Fixtures.Prover.insert_into_a_set "prover.ensures");
  Harness.test "a map holds an inserted value under its key" (fun () ->
      expect_proven Fixtures.Prover.map_insert);
  Harness.test "a map keeps its other keys' values" (fun () ->
      expect_proven Fixtures.Prover.map_insert_keeping_another_key);
  Harness.test "a value read from a map is the value assigned to an equal key" (fun () ->
      expect_proven Fixtures.Prover.value_read_after_assign);
  Harness.test "a value indexed in a map is the value inserted under an equal key" (fun () ->
      expect_proven Fixtures.Prover.value_indexed_after_insert);
  Harness.test "a loop invariant bounds every value of a map" (fun () ->
      expect_proven Fixtures.Prover.word_count_bounded_by_its_index)

let () =
  Harness.test "a list literal of three hundred elements has its length and each element" (fun () ->
      expect_proven Fixtures.Prover.list_literal_of_three_hundred_elements);
  Harness.test "a loop that moves the elements out of a list visits the list's elements in order"
    (fun () -> expect_proven Fixtures.Prover.owned_loop_moving_each_element);
  Harness.test "a loop that moves the elements out of a list visits as many as the list holds"
    (fun () -> expect_proven Fixtures.Prover.owned_loop_counting_its_elements);
  Harness.test "a loop that moves the elements out of an array visits the array's elements"
    (fun () -> expect_proven Fixtures.Prover.owned_loop_over_an_array);
  Harness.test "a loop that moves the elements out of a set visits members of the set" (fun () ->
      expect_proven Fixtures.Prover.owned_loop_over_a_set);
  Harness.test "a cursor pulled again after a `break` gives the elements that it had left"
    (fun () -> expect_proven Fixtures.Prover.cursor_pulled_again_after_a_break);
  Harness.test "a loop that names `visited` proves that its cursor gives its model in order"
    (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"the `next` of its cursor may not give the values of the cursor's `model()` in order"
        Fixtures.Prover.visited_over_a_cursor_that_gives_its_model_backward "prover.invariant");
  Harness.test "a loop that does not name `visited` asks nothing of its cursor's model" (fun () ->
      expect_proven Fixtures.Prover.cursor_that_gives_its_model_backward);
  Harness.test "a map literal holds each key's value" (fun () ->
      expect_proven Fixtures.Prover.map_literal_read);
  Harness.test "a map literal's keys must be distinct" (fun () ->
      expect_not_proven Fixtures.Prover.map_literal_with_a_repeated_key "prover.requires");
  Harness.test "a set literal contains its listed elements and nothing else" (fun () ->
      expect_proven Fixtures.Prover.set_literal_contains);
  Harness.test "a set literal of sixteen elements has its members and its length" (fun () ->
      expect_proven Fixtures.Prover.set_literal_of_sixteen_elements);
  Harness.test "a map literal of one hundred keys has distinct keys" (fun () ->
      expect_proven Fixtures.Prover.map_literal_of_one_hundred_keys);
  Harness.test "a set literal may repeat an element" (fun () ->
      expect_proven Fixtures.Prover.set_literal_with_a_repeated_element);
  Harness.test "a sorted map literal's keys must be distinct" (fun () ->
      expect_not_proven Fixtures.Prover.sorted_map_literal_with_a_repeated_key "prover.requires");
  Harness.test "a deque literal has its length and is one allocation" (fun () ->
      expect_proven Fixtures.Prover.deque_literal_length);
  Harness.test "an empty sorted set literal is empty and takes constant time" (fun () ->
      expect_proven Fixtures.Prover.empty_sorted_set_literal);
  Harness.test "a literal of a type that implements FromElements is proven against its impl"
    (fun () -> expect_proven Fixtures.Prover.literal_of_a_type_with_from_elements);
  Harness.test "a provided implementation's calls keep the capability's contract" (fun () ->
      expect_proven (dice ^ Fixtures.Prover.fixed_dice_provided));
  Harness.test "an implementation of a capability keeps the capability's contract" (fun () ->
      expect_not_proven (dice ^ Fixtures.Prover.loaded_dice_rolling_nine) "prover.ensures");
  Harness.test "a capability's broken contract is named as the capability's" (fun () ->
      let actual = read_message (dice ^ Fixtures.Prover.loaded_dice_rolling_nine) in
      if not (String.includes ~affix:"The capability's `result >= 1 && result <= 6`" actual) then
        Harness.fail "found: %s" actual);
  Harness.test "an implementation of a capability that keeps its contract proves" (fun () ->
      expect_proven (dice ^ Fixtures.Prover.fair_dice));
  Harness.test "let else continues where its pattern matched" (fun () ->
      expect_proven Fixtures.Prover.let_else_of_an_option);
  Harness.test "a quantifier's pattern takes each element apart" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_span_fields);
  Harness.test "a quantifier over a range may ignore its index" (fun () ->
      expect_proven Fixtures.Prover.quantifier_ignoring_its_index);
  Harness.test "a quantifier over a list ranges over its elements" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_positive_items);
  Harness.test "a quantifier over a list in a body equals one over its indices" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_items_in_a_body);
  Harness.test "a quantifier's pattern in a body takes each element apart" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_span_fields_in_a_body);
  Harness.test "a quantifier over a list in a body may be false" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_items_in_a_body_ensured_true
        "prover.ensures");
  Harness.test "a quantifier in a body reads the collection's `count` and `element`" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_counted_elements_in_a_body);
  Harness.test "a quantifier in a specification reads the collection's `count` and `element`"
    (fun () -> expect_proven Fixtures.Prover.specification_quantifier_over_counted_elements);
  Harness.test "a postcondition that fixes a call's result is the call's value" (fun () ->
      expect_proven Fixtures.Prover.specification_quantifier_over_twins_read_through_a_field);
  Harness.test "a postcondition through a type's own `==` does not fix a call's value" (fun () ->
      expect_not_proven Fixtures.Prover.postcondition_through_a_hand_written_equal "prover.ensures");
  Harness.test "a quantifier's pattern leaves out the elements it does not match" (fun () ->
      expect_proven Fixtures.Prover.specification_quantifier_with_a_refutable_pattern);
  Harness.test "a quantifier over a range value reads the range's `count` and `element`" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_a_range_value);
  Harness.test
    "a quantifier in a body over a set reaches every member once the theorem that relates them is \
     called" (fun () -> expect_proven Fixtures.Prover.quantifier_over_set_members_in_a_body)

let () =
  Harness.test "a postcondition of a view's method holds of the `String` it was called on"
    (fun () -> expect_proven Fixtures.Prover.to_string_of_a_string_keeps_its_length);
  Harness.test "a postcondition of a view's `mut` method holds of the `List` it was called on"
    (fun () -> expect_proven Fixtures.Prover.sort_of_a_list_sorts_it);
  Harness.test "a postcondition of a view's lending method holds of the `List` it was called on"
    (fun () -> expect_proven Fixtures.Prover.first_of_a_list_is_some_when_it_has_elements);
  Harness.test "a postcondition of a view's `mut` method holds of the `Array` it was called on"
    (fun () -> expect_proven Fixtures.Prover.sort_of_an_array_sorts_it);
  Harness.test "a postcondition of a view's lending method holds of the `Array` it was called on"
    (fun () -> expect_proven Fixtures.Prover.first_of_an_array_is_some)

let swap = Fixtures.Prover.exchange

let () =
  Harness.test "two elements lent together must be different elements" (fun () ->
      expect_not_proven
        (swap ^ Fixtures.Prover.exchange_of_two_elements)
        "prover.disjoint"
        ~fixed:
          ( "requires first < items.length() && second < items.length()\n\
             {\n\
            \  exchange(mut items[first], second: mut items[second])",
            "requires first < items.length() && second < items.length()\n\
            \  requires first != second\n\
             {\n\
            \  exchange(mut items[first], second: mut items[second])" ));
  Harness.test "two different elements can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_distinct_elements));
  Harness.test "elements of two ranges lent together must be in ranges that do not overlap"
    (fun () ->
      expect_not_proven
        (swap ^ Fixtures.Prover.exchange_of_elements_of_overlapping_ranges)
        "prover.disjoint");
  Harness.test "elements of two ranges that do not overlap can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_elements_of_disjoint_ranges));
  Harness.test "elements of two ranges of ranges that do not overlap can be lent together"
    (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_elements_of_disjoint_ranges_of_ranges));
  Harness.test "elements of two ranges of ranges lent together must be different elements"
    (fun () ->
      expect_not_proven
        (swap ^ Fixtures.Prover.exchange_of_elements_of_overlapping_ranges_of_ranges)
        "prover.disjoint");
  Harness.test "an element reached through a range and directly is one element" (fun () ->
      expect_not_proven
        (swap ^ Fixtures.Prover.exchange_of_one_element_through_a_range_and_directly)
        "prover.disjoint");
  Harness.test "different elements of two equal ranges can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_elements_of_two_equal_ranges));
  Harness.test "elements of different rows of a range of rows can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_elements_of_two_rows_of_a_range));
  Harness.test "an element of a range lent `mut` must not be the element that an argument views"
    (fun () ->
      expect_not_proven Fixtures.Prover.element_of_a_range_pushed_onto_itself "prover.disjoint");
  Harness.test "parallel branches that mutate elements must mutate different ones" (fun () ->
      expect_not_proven Fixtures.Prover.parallel_branches_assigning_two_elements "prover.disjoint"
        ~fixed:
          ( "requires first < items.length() && second < items.length()\n{\n  parallel {",
            "requires first < items.length() && second < items.length()\n\
            \  requires first != second\n\
             {\n\
            \  parallel {" ))

let () =
  Harness.test "self mutated on one path is joined with the other" (fun () ->
      expect_not_proven Fixtures.Prover.box_set_on_one_path "prover.ensures");
  Harness.test "a lending method's `ensures` holds for the part lent on each path" (fun () ->
      expect_not_proven Fixtures.Prover.maybe_part_lent_on_each_path "prover.ensures"
        ~fixed:
          ( "ensures result == self.value\n{\n  if self.present {",
            "ensures result == self.value\n\
            \  requires (!self.present) ==> (self.other == self.value)\n\
             {\n\
            \  if self.present {" ))

let () =
  Harness.test "a loop forgets a list it mutates through a method" (fun () ->
      expect_not_proven Fixtures.Prover.loop_pushing_onto_a_list "prover.assertion");
  Harness.test "a loop forgets a record whose field it assigns" (fun () ->
      expect_not_proven Fixtures.Prover.loop_assigning_a_box_field "prover.assertion");
  Harness.test "a loop forgets self when it mutates it" (fun () ->
      expect_not_proven Fixtures.Prover.box_fill_loop "prover.assertion");
  Harness.test "a loop forgets a place that it provides `mut`" (fun () ->
      expect_not_proven Fixtures.Prover.marker_provided_mut_in_a_loop "prover.assertion");
  Harness.test "a `return` from a `provide mut` forgets the provided place" (fun () ->
      expect_not_proven Fixtures.Prover.provider_state_after_a_return_inside_provide
        "prover.ensures");
  Harness.test
    "an early exit from a `concurrent` block in a `provide mut` forgets the provided place"
    (fun () ->
      expect_not_proven Fixtures.Prover.provider_state_after_a_concurrent_early_exit
        "prover.ensures")

let constant_step = Fixtures.Prover.constant_step

let () =
  Harness.test "a body with no calls is O(1)" (fun () ->
      expect_proven Fixtures.Prover.constant_body_of_time_o_1);
  Harness.test "calls to O(1) functions are O(1)" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.step_of_a_step));
  Harness.test "a call to a function with no bound on its time" (fun () ->
      expect_not_proven Fixtures.Prover.call_of_a_callee_without_a_time_clause "prover.cost");
  Harness.test "a loop over a range is linear" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.range_loop_of_linear_time));
  Harness.test "a loop over a range is not constant" (fun () ->
      expect_not_proven (constant_step ^ Fixtures.Prover.range_loop_of_constant_time) "prover.cost");
  Harness.test "a callee's cost of a constant amount of any size meets every O bound" (fun () ->
      expect_proven Fixtures.Prover.table_of_a_constant_size_in_linear_time;
      expect_proven Fixtures.Prover.callee_of_a_large_constant_time);
  Harness.test "a callee's cost with a constant factor of any size meets the bound without it"
    (fun () -> expect_proven Fixtures.Prover.callee_of_a_constant_factor_in_linear_time);
  Harness.test "a callee's cost that grows with an argument is not constant, whatever its constants"
    (fun () ->
      expect_not_proven Fixtures.Prover.callee_of_a_constant_factor_in_constant_time "prover.cost";
      expect_not_proven Fixtures.Prover.callee_of_its_argument_and_a_large_constant_in_constant_time
        "prover.cost");
  Harness.test "a bound's method whose impl states a constant time of any size is constant"
    (fun () -> expect_proven Fixtures.Prover.weigh_of_an_impl_in_a_large_constant_time);
  Harness.test "a loop with a constant count of any size meets every O bound" (fun () ->
      expect_proven Fixtures.Prover.range_loop_of_a_large_constant_count;
      expect_proven Fixtures.Prover.while_loop_of_a_large_constant_count;
      expect_proven Fixtures.Prover.large_constant_loops_per_element);
  Harness.test "a loop with a constant count of iterations that grow with an input is not constant"
    (fun () -> expect_not_proven Fixtures.Prover.large_constant_loop_of_linear_calls "prover.cost");
  Harness.test "a loop with a constant count of recursive calls counts every call" (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_constant_loop "prover.cost");
  Harness.test "a loop's cost clause around two recursive calls does not make them linear"
    (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_range_loop_with_a_cost_clause
        "prover.cost";
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_while_loop_with_a_cost_clause
        "prover.cost";
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_cursor_loop_with_a_cost_clause
        "prover.cost");
  Harness.test "nested loops' cost clauses around two recursive calls do not make them linear"
    (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_nested_loops_with_cost_clauses
        "prover.cost");
  Harness.test
    "a loop's cost clause in a lambda around two recursive calls does not make them linear"
    (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_loop_with_a_cost_clause_in_a_lambda
        "prover.cost");
  Harness.test "a loop's cost clause around one recursive call is linear" (fun () ->
      expect_proven Fixtures.Prover.one_recursive_call_in_a_range_loop_with_a_cost_clause;
      expect_proven Fixtures.Prover.one_recursive_call_in_a_while_loop_with_a_cost_clause);
  Harness.test "a loop's cost clause beside a recursive call counts the loop as its clause's order"
    (fun () -> expect_proven Fixtures.Prover.loop_with_a_cost_clause_beside_a_recursive_call);
  Harness.test "a callee that runs a lambda with a recursive call twice is not linear" (fun () ->
      expect_not_proven Fixtures.Prover.recursive_call_in_a_lambda_that_its_callee_runs_twice
        "prover.cost");
  Harness.test
    "a callee that runs a constant-time lambda with a recursive call twice is not constant"
    (fun () ->
      expect_not_proven
        Fixtures.Prover.recursive_call_in_a_constant_time_lambda_that_its_callee_runs_twice
        "prover.cost");
  Harness.test "a function value that runs a lambda with a recursive call twice is not constant"
    (fun () ->
      expect_not_proven Fixtures.Prover.recursive_call_in_a_lambda_that_a_function_value_runs_twice
        "prover.cost");
  Harness.test "two recursive calls in a lambda under an amortized bound are not linear" (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_in_a_lambda_under_an_amortized_bound
        "prover.cost");
  Harness.test "nested loops over ranges are quadratic" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.nested_range_loops_of_quadratic_time));
  Harness.test "a loop whose iterations cost their index is quadratic" (fun () ->
      expect_proven Fixtures.Prover.work_with_iterations_costing_their_index);
  Harness.test "a loop over a list takes time linear in its length" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.list_loop_of_linear_time));
  Harness.test "an iteration's cost is the larger of its branches'" (fun () ->
      expect_proven Fixtures.Prover.loop_with_branches_of_different_costs);
  Harness.test "a while loop runs at most its measure's times" (fun () ->
      expect_proven Fixtures.Prover.while_loop_with_a_measure);
  Harness.test "recursion on one less is linear" (fun () ->
      expect_proven Fixtures.Prover.recursion_on_one_less_of_linear_time);
  Harness.test "recursion on one less is not constant" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_on_one_less_of_constant_time "prover.cost");
  Harness.test "recursion on half is logarithmic" (fun () ->
      expect_proven Fixtures.Prover.recursion_on_half);
  Harness.test "functions that call each other in a cycle share their constants" (fun () ->
      expect_proven Fixtures.Prover.even_and_odd_of_linear_time);
  Harness.test "a quantifier in code runs over its range" (fun () ->
      expect_proven Fixtures.Prover.all_positive);
  Harness.test "calls through a function value are counted exactly" (fun () ->
      expect_proven Fixtures.Prover.each_visiting_once_per_element);
  Harness.test "calling a function value twice per element is not once" (fun () ->
      expect_not_proven Fixtures.Prover.each_visiting_twice_per_element "prover.cost");
  Harness.test "a caller counts the calls its callee promises" (fun () ->
      expect_proven Fixtures.Prover.calls_of_visit_counted);
  Harness.test "a loop's cost clause bounds its cost so far" (fun () ->
      expect_proven Fixtures.Prover.while_loop_with_a_cost_clause);
  Harness.test "a function value with an O(1) type is one unit" (fun () ->
      expect_proven Fixtures.Prover.run_of_a_constant_time_transform);
  Harness.test "a lambda must meet its type's cost" (fun () ->
      expect_not_proven Fixtures.Prover.spinning_lambda_passed_as_constant_time "prover.cost");
  Harness.test "nothing allocates without a block to allocate" (fun () ->
      expect_proven Fixtures.Prover.sum_with_no_allocations);
  Harness.test "building an indirect variant allocates" (fun () ->
      expect_not_proven Fixtures.Prover.tree_node_built "prover.cost");
  Harness.test "an indirect variant is one allocation" (fun () ->
      expect_proven Fixtures.Prover.tree_node_with_one_allocation);
  Harness.test "a recursive call's quantified ensures reads a field under its quantifier" (fun () ->
      expect_proven Fixtures.Prover.tree_insert_keeping_every_key);
  Harness.test
    "an obligation whose quantified facts exhaust the steps is proven from its ground facts"
    (fun () -> expect_proven Fixtures.Prover.product_bound_beside_a_growing_measure);
  Harness.test "nested loops are not linear" (fun () ->
      expect_not_proven
        (constant_step ^ Fixtures.Prover.nested_range_loops_ensured_linear)
        "prover.cost");
  Harness.test "two recursive calls on one less are not linear" (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_on_one_less "prover.cost");
  Harness.test "functions in a cycle that branch are not linear" (fun () ->
      expect_not_proven Fixtures.Prover.branching_ping_and_pong "prover.cost");
  Harness.test "a callback's time is not free" (fun () ->
      expect_not_proven Fixtures.Prover.each_visiting_a_callback_without_a_time_clause "prover.cost");
  Harness.test "calls through a lambda that captures the function value are not known" (fun () ->
      expect_not_proven Fixtures.Prover.each_visiting_through_a_capturing_lambda "prover.cost");
  Harness.test "a quantifier over a costly body is not linear" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_a_spinning_body "prover.cost");
  Harness.test "a loop's cost clause that is too small" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_with_a_small_cost_clause "prover.cost");
  Harness.test "calls of a capability's method are counted" (fun () ->
      expect_proven Fixtures.Prover.meter_ticks_counted);
  Harness.test
    "a call inside a `provide` whose implementation uses the capability has no known count"
    (fun () ->
      expect_not_proven Fixtures.Prover.calls_through_a_provider_that_uses_the_capability
        "prover.cost");
  Harness.test "a call inside a `provide` whose implementation uses nothing reaches no caller"
    (fun () -> expect_proven Fixtures.Prover.calls_through_a_provider_that_uses_nothing);
  Harness.test
    "a call to a provider of another capability that uses the counted one has no known count"
    (fun () ->
      expect_not_proven Fixtures.Prover.calls_through_a_provider_of_another_capability "prover.cost");
  Harness.test "a `provide` that `break` leaves takes no calls after the loop" (fun () ->
      expect_proven Fixtures.Prover.calls_after_a_provide_left_by_break);
  Harness.test "a capability method that uses another capability may call it any number of times"
    (fun () ->
      expect_not_proven Fixtures.Prover.calls_of_a_capability_method_that_uses_another "prover.cost");
  Harness.test "a callee's allocations add up" (fun () ->
      expect_proven Fixtures.Prover.tree_built_by_callees);
  Harness.test "a lambda's time is bounded where it is written" (fun () ->
      expect_proven Fixtures.Prover.each_visiting_with_a_bounded_lambda);
  Harness.test "a lambda that loops over its argument has no bound" (fun () ->
      let actual = list_codes Fixtures.Prover.each_visiting_with_a_looping_lambda in
      if not (List.mem "prover.cost" actual) then Harness.fail "%s" (String.concat ", " actual));
  Harness.test "a loop's cost clause over its received parts" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.list_loop_with_a_cost_clause));
  Harness.test "an impl's method keeps its trait's cost" (fun () ->
      expect_not_proven Fixtures.Prover.sized_impl_with_the_traits_cost "prover.cost")

let () =
  let callees = Fixtures.Prover.meter_and_step in
  let expect_with_the_last ~without ~with_ =
    expect_not_proven (callees ^ without) "prover.cost";
    expect_proven (callees ^ with_)
  in
  Harness.test
    "a `while` loop's `<=` clause leaves out the evaluation of the condition that ends it"
    (fun () ->
      expect_with_the_last
        ~without:Fixtures.Prover.polls_of_a_while_condition_bounded_without_the_last
        ~with_:Fixtures.Prover.polls_of_a_while_condition_bounded_with_the_last);
  Harness.test
    "a `while` loop's `==` clause leaves out the evaluation of the condition that ends it"
    (fun () ->
      expect_with_the_last
        ~without:Fixtures.Prover.ticks_of_a_while_condition_counted_without_the_last
        ~with_:Fixtures.Prover.ticks_of_a_while_condition_counted_with_the_last);
  Harness.test "the operand of `||` that is evaluated only where a `while` loop ends is counted"
    (fun () ->
      expect_with_the_last
        ~without:Fixtures.Prover.tick_of_the_operand_that_ends_a_while_counted_as_none
        ~with_:Fixtures.Prover.tick_of_the_operand_that_ends_a_while_counted);
  Harness.test "an inner loop's last evaluation of its condition is counted in the outer iteration"
    (fun () ->
      expect_with_the_last
        ~without:Fixtures.Prover.ticks_of_an_inner_while_condition_counted_without_the_last
        ~with_:Fixtures.Prover.ticks_of_an_inner_while_condition_counted_with_the_last);
  Harness.test "a loop whose condition and whose exit spend nothing keeps its exact count"
    (fun () ->
      expect_proven (callees ^ Fixtures.Prover.ticks_in_the_body_of_a_while_with_a_clause_counted);
      expect_proven
        (callees ^ Fixtures.Prover.ticks_in_the_body_of_a_list_loop_with_a_clause_counted));
  Harness.test "the allocations of the evaluation of the condition that ends a `while` are counted"
    (fun () ->
      let grows = Fixtures.Prover.grows_allocating_once in
      expect_not_proven
        (grows ^ Fixtures.Prover.allocations_of_a_while_condition_bounded_without_the_last)
        "prover.cost";
      expect_proven (grows ^ Fixtures.Prover.allocations_of_a_while_condition_bounded_with_the_last));
  Harness.test "the time of the evaluation of the condition that ends a `while` is counted"
    (fun () ->
      let costly = Fixtures.Prover.costly_refusing_in_linear_time in
      expect_not_proven
        (costly ^ Fixtures.Prover.time_of_the_operand_that_ends_a_while_left_out)
        "prover.cost";
      expect_proven (costly ^ Fixtures.Prover.time_of_the_operand_that_ends_a_while_counted))

let () =
  let ticking = Fixtures.Prover.ticking_countdown in
  Harness.test "a pulled `next` that uses a capability makes its calls of the capability's method"
    (fun () ->
      expect_not_proven
        (ticking ^ Fixtures.Prover.ticks_of_a_pulled_next_counted_as_none)
        "prover.cost";
      expect_not_proven
        (ticking ^ Fixtures.Prover.ticks_of_a_pulled_next_bounded_by_none)
        "prover.cost");
  Harness.test "a loop over a cursor counts the `next` that returns `None`" (fun () ->
      expect_not_proven
        (ticking ^ Fixtures.Prover.ticks_of_a_cursor_loop_bounded_without_the_last_next)
        "prover.cost";
      expect_proven (ticking ^ Fixtures.Prover.ticks_of_a_cursor_loop_counted_with_the_last_next));
  Harness.test "the allocations of the `next` that returns `None` are counted" (fun () ->
      let allocating = Fixtures.Prover.allocating_countdown in
      expect_not_proven
        (allocating ^ Fixtures.Prover.allocations_of_a_cursor_loop_bounded_without_the_last_next)
        "prover.cost";
      expect_proven
        (allocating ^ Fixtures.Prover.allocations_of_a_cursor_loop_bounded_with_the_last_next));
  Harness.test "the time of the `next` that returns `None` is counted" (fun () ->
      let weighted = Fixtures.Prover.weighted_countdown in
      expect_not_proven
        (weighted ^ Fixtures.Prover.time_of_a_cursor_loop_without_the_last_next)
        "prover.cost";
      expect_proven (weighted ^ Fixtures.Prover.time_of_a_cursor_loop_with_the_last_next))

let meter = Fixtures.Prover.meter

let () =
  Harness.test "saving and spending potential are amortized O(1)" (fun () -> expect_proven meter);
  Harness.test "spending potential is not O(1) without it" (fun () ->
      expect_not_proven Fixtures.Prover.meter_spend_not_amortized "prover.cost");
  Harness.test "a plain bound pays for the potential it is given" (fun () ->
      expect_proven (meter ^ Fixtures.Prover.meter_spend_within_its_credit));
  Harness.test "a plain bound that does not pay for the potential it uses" (fun () ->
      expect_not_proven (meter ^ Fixtures.Prover.meter_spend_in_constant_time) "prover.cost");
  Harness.test "a loop that spends potential telescopes" (fun () ->
      expect_proven (meter ^ Fixtures.Prover.meter_spent_within_its_credit));
  Harness.test "a loop that spends potential it was given is not linear in its count" (fun () ->
      let actual = list_codes (meter ^ Fixtures.Prover.meter_spent_in_linear_time) in
      if actual <> [ "prover.cost" ] then Harness.fail "%s" (String.concat ", " actual));
  Harness.test "a list's potential is its elements', through its model" (fun () ->
      expect_proven (meter ^ Fixtures.Prover.keep_of_a_list_of_meters));
  let encoder = "type Encoder(bytes: List[UInt8])\n\n" in
  Harness.test "a record with no potential clause holds its parts'" (fun () ->
      expect_proven (encoder ^ Fixtures.Prover.encoder_uint8));
  Harness.test "the potential of a type that holds itself is read" (fun () ->
      expect_proven Fixtures.Prover.chain_potential);
  Harness.test "a loop that pushes into a record's list is amortized linear" (fun () ->
      expect_proven (encoder ^ Fixtures.Prover.encoder_bytes));
  let bag = Fixtures.Prover.bag in
  Harness.test "a method that lends a part `mut` is not charged for the caller's mutations of it"
    (fun () -> expect_proven bag);
  Harness.test "a caller that raises a lent part's potential pays for it" (fun () ->
      let actual =
        list_codes (meter ^ bag ^ Fixtures.Prover.meter_credit_raised_through_a_lent_part)
      in
      if actual <> [ "prover.cost" ] then Harness.fail "%s" (String.concat ", " actual));
  Harness.test "a caller that lowers a lent part's potential is paid by it" (fun () ->
      expect_proven (meter ^ bag ^ Fixtures.Prover.meter_credit_spent_through_a_lent_part));
  Harness.test "a write that raises a declared potential pays for it" (fun () ->
      expect_not_proven Fixtures.Prover.credit_set_by_a_write "prover.cost");
  Harness.test "a value that a provided capability changes pays for its potential" (fun () ->
      expect_not_proven
        (meter ^ Fixtures.Prover.meter_credit_raised_by_a_provided_capability)
        "prover.cost");
  Harness.test "a callee with only a plain bound pays for the potential of its result" (fun () ->
      expect_not_proven
        (meter ^ Fixtures.Prover.meter_built_by_a_plain_callee_then_spent)
        "prover.cost");
  Harness.test "a construction pays for the potential its type declares" (fun () ->
      expect_proven (meter ^ Fixtures.Prover.meter_built_with_its_credit));
  Harness.test "a construction whose potential exceeds the bound is not amortized constant"
    (fun () ->
      expect_not_proven (meter ^ Fixtures.Prover.meter_built_in_constant_time) "prover.cost");
  Harness.test "a type that declares a potential is not `Plain`" (fun () ->
      expect_not_proven
        (meter ^ Fixtures.Prover.meter_copied_implicitly)
        "ownership.not_owned"
        ~fixed:("var copy = meter", "var copy = meter.copy()")
        ~left_after_fix:[ "prover.cost" ];
      expect_not_proven Fixtures.Prover.plain_credit_declared "types.cannot_derive");
  Harness.test "a type parameter bounded by `Plain` holds no potential" (fun () ->
      expect_proven Fixtures.Prover.plain_values_read_twice);
  Harness.test "a view holds no potential of the elements it reaches" (fun () ->
      expect_not_proven (meter ^ Fixtures.Prover.meters_held_then_spent) "prover.cost";
      expect_not_proven (meter ^ Fixtures.Prover.meter_packed_with_a_view) "prover.cost");
  Harness.test "a function with a plain bound does not convert to an amortized function type"
    (fun () ->
      expect_not_proven
        (meter ^ Fixtures.Prover.plain_function_passed_as_an_amortized_callback)
        "types.mismatch");
  Harness.test "a capability method's bound counts the change in its provider's potential"
    (fun () ->
      expect_not_proven (meter ^ Fixtures.Prover.meter_deposit_provided) "prover.cost";
      expect_proven (meter ^ Fixtures.Prover.meter_ticked_by_a_provided_capability);
      expect_proven Fixtures.Prover.values_collected_by_a_provided_capability);
  Harness.test "a cancelled branch's change to a value pays for its potential" (fun () ->
      expect_not_proven (meter ^ Fixtures.Prover.meter_raised_in_a_cancelled_branch) "prover.cost");
  Harness.test "an amortized loop over an owned list is linear" (fun () ->
      expect_proven Fixtures.Prover.amortized_loop_over_an_owned_list);
  Harness.test "a string's bytes move in amortized constant time" (fun () ->
      expect_proven Fixtures.Prover.amortized_length_of_owned_bytes);
  Harness.test "a potential below zero" (fun () ->
      expect_not_proven "type Debt(owed: Int64)\n  cost potential owed\n" "prover.cost");
  Harness.test "a potential its invariant keeps at or above zero" (fun () ->
      expect_proven Fixtures.Prover.debt_potential)

let count_holes ?(in_ = fun (_ : Path.t) -> true) text =
  let packages = Support.setup [ ("app.main", text) ] in
  let prove_key =
    Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main")
  in
  List.fold_left
    (fun total (declaration : Resolve.Names.declaration) ->
      match prove_key declaration.key with
      | Obligations outcome when in_ declaration.key.path -> total + List.length outcome.holes
      | Obligations _ | Unsupported _ | Not_proven_here -> total)
    0
    (Support.list_declarations packages (Support.parse_module "app.main"))

let is_function name (path : Path.t) =
  match path with Top { name = top; _ } -> top = name | _ -> false

let is_impl (path : Path.t) = match path with Impl _ -> true | _ -> false

let () =
  Harness.test "a todo in a theorem is a hole, not a failure" (fun () ->
      let text = Fixtures.Prover.theorem_of_todo in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "a todo in a contract is a hole where it is written and where it is relied on"
    (fun () ->
      List.iter
        (fun (text, holes) ->
          expect_proven text;
          if count_holes text <> holes then Harness.fail "%d holes" (count_holes text))
        [
          (Fixtures.Prover.todo_requires_with_a_caller, 2);
          (Fixtures.Prover.todo_ensures_with_a_caller, 4);
          (Fixtures.Prover.positive_with_a_todo_invariant, 2);
        ]);
  Harness.test "a todo in a proof block leaves the rest of its path to it" (fun () ->
      let text = Fixtures.Prover.proof_block_of_todo in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "a contract on a body that is not written waits for it, and the todo is a hole"
    (fun () ->
      let text = Fixtures.Prover.todo_body_with_an_ensures in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "the code before a todo is still proven" (fun () ->
      expect_not_proven Fixtures.Prover.element_read_before_a_todo "prover.out_of_bounds");
  Harness.test "a constant, a field default, or a parameter default left todo is read" (fun () ->
      expect_proven Fixtures.Prover.values_left_todo);
  Harness.test "a constant left todo has an unknown value" (fun () ->
      expect_not_proven Fixtures.Prover.increment_of_a_todo_constant "prover.overflow"
        ~fixed:("fn above_limit() -> Int64 {", "fn above_limit() -> Int64\n  uses Panic\n{"));
  Harness.test "an impl's laws wait while one of its methods is not written" (fun () ->
      expect_proven Fixtures.Prover.meters_equal_left_todo);
  Harness.test "a type that contains itself through a map's values is read" (fun () ->
      expect_proven Fixtures.Prover.tree_of_maps)

let () =
  Harness.test "a lambda's result is in range only for arguments in range" (fun () ->
      expect_not_proven Fixtures.Prover.same_lambda_in_range "prover.ensures");
  Harness.test "a lambda's result is in range only for arguments whose fields are in range"
    (fun () ->
      expect_not_proven Fixtures.Prover.lambda_reading_a_field_passed_to_a_function "prover.ensures"
        ~fixed:
          ( "ensures result <= 0\n{\n  let _ = ignore(fn(e) { e.value })",
            "ensures result <= 0\n  requires x <= 0\n{\n  let _ = ignore(fn(e) { e.value })" ));
  Harness.test "an uncalled lambda's calls show nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.lambda_calling_a_hang_uncalled "prover.ensures"
        ~fixed:
          ( "ensures result <= 0\n{\n  if x > 0 {",
            "ensures result <= 0\n  requires x <= 0\n{\n  if x > 0 {" ));
  Harness.test "a lambda whose arguments cannot meet its requires shows nothing of the path"
    (fun () ->
      expect_not_proven Fixtures.Prover.each_index_with_an_unreachable_lambda "prover.ensures"
        ~fixed:
          ( "ensures result <= 0\n{\n  if x > 0 {",
            "ensures result <= 0\n  requires x <= 0\n{\n  if x > 0 {" ));
  Harness.test "a quantifier over an empty range shows nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_an_empty_range_after_a_hang "prover.ensures"
        ~fixed:
          ( "ensures result <= 0\n{\n  if x > 0 {",
            "ensures result <= 0\n  requires x <= 0\n{\n  if x > 0 {" ));
  Harness.test "a lambda over a type no value has shows nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.lambda_over_an_empty_type "prover.ensures"
        ~fixed:
          ( "ensures result <= 0\n{\n  if x > 0 {",
            "ensures result <= 0\n  requires x <= 0\n{\n  if x > 0 {" ));
  Harness.test "a todo in a law's proof is a hole that stands for the law" (fun () ->
      let text =
        monoid ^ make_flag_impl_source "true"
        ^ "\nproof Monoid.left_identity for Flag {\n  todo\n}\n"
      in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text))

let () =
  Harness.test "a trait's ensures holds of an impl's method only where the trait's requires does"
    (fun () -> expect_not_proven Fixtures.Prover.scaled_impl "prover.ensures");
  Harness.test "a law of an unfinished impl is a hole where it is assumed" (fun () ->
      let text = Fixtures.Prover.sized_law_of_an_unfinished_impl in
      let holes = count_holes ~in_:(is_function "f") text in
      if holes <> 1 then Harness.fail "%d holes" holes);
  Harness.test "an unfinished impl of a trait with a law holds each todo as a hole" (fun () ->
      let holes = count_holes ~in_:is_impl Fixtures.Prover.sized_law_of_an_unfinished_impl in
      if holes <> 1 then Harness.fail "%d holes" holes);
  Harness.test "an unfinished impl of a trait without laws holds no hole" (fun () ->
      let holes = count_holes ~in_:is_impl Fixtures.Prover.box_of_an_unfinished_impl_without_laws in
      if holes <> 0 then Harness.fail "%d holes" holes);
  Harness.test "a law whose proof holds a todo is a hole where it is assumed" (fun () ->
      let text = Fixtures.Prover.zero_law_with_a_todo_proof in
      if count_holes text <> 2 then Harness.fail "%d holes" (count_holes text));
  Harness.test "each impl of a trait with arguments keeps its own laws" (fun () ->
      expect_not_proven Fixtures.Prover.scale_impls_with_their_own_laws "prover.law");
  Harness.test "an element mutated through a lend meets its invariant when the lend ends" (fun () ->
      expect_not_proven Fixtures.Prover.span_low_raised_through_a_lend "prover.invariant");
  Harness.test "an element mutated through a lend that keeps its invariant proves" (fun () ->
      expect_proven Fixtures.Prover.span_high_raised_through_a_lend);
  Harness.test "an element meets its invariant when a step on it returns" (fun () ->
      expect_not_proven Fixtures.Prover.step_on_a_list_element_breaking_its_invariant
        "prover.invariant";
      expect_not_proven Fixtures.Prover.step_on_the_element_of_a_loop_breaking_its_invariant
        "prover.invariant");
  Harness.test "a value that a step left breaking its invariant is checked when it is passed"
    (fun () ->
      expect_not_proven Fixtures.Prover.value_passed_to_a_call_after_a_step_broke_its_invariant
        "prover.invariant");
  Harness.test "a step on an element that restores its invariant proves" (fun () ->
      expect_proven Fixtures.Prover.step_on_a_list_element_restoring_its_invariant);
  Harness.test "an element's invariant is proven from the ensures of a call that changes a part"
    (fun () ->
      expect_proven Fixtures.Prover.call_changing_a_part_of_a_list_element_within_its_invariant;
      expect_not_proven Fixtures.Prover.call_changing_a_part_of_a_list_element_past_its_invariant
        "prover.invariant");
  Harness.test "a lent part meets its invariant" (fun () ->
      let packages = Support.setup [ ("app.main", Fixtures.Prover.positive_lent_by_a_source) ] in
      let messages =
        List.map
          (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
          (check packages (Support.parse_file "app.main"))
      in
      if not (List.exists (String.includes ~affix:"may not hold for the part lent here") messages)
      then Harness.fail "%s" (String.concat "; " messages));
  Harness.test "a loop keeps the validity of each value it mutates" (fun () ->
      expect_proven Fixtures.Prover.positive_reassigned_in_a_loop);
  Harness.test "an iteration must keep the validity of each value the loop mutates" (fun () ->
      expect_not_proven Fixtures.Prover.positive_zeroed_in_a_loop "prover.invariant")

let () =
  Harness.test "a mut range's bounds are evaluated once" (fun () ->
      expect_not_proven Fixtures.Prover.mut_range_with_counted_bounds "prover.ensures");
  Harness.test "a while condition's mut argument mutates the loop's state" (fun () ->
      expect_not_proven Fixtures.Prover.while_condition_stepping_a_count "prover.ensures");
  Harness.test "a match mut binding is written back to the scrutinee" (fun () ->
      expect_not_proven Fixtures.Prover.match_mut_on_an_option "prover.ensures");
  Harness.test "a while condition's cost is the iteration's" (fun () ->
      expect_not_proven Fixtures.Prover.hits_in_a_while_condition "prover.cost");
  Harness.test "the right operand of || is counted at its cost" (fun () ->
      expect_not_proven Fixtures.Prover.hits_in_the_right_operand_of_or "prover.cost");
  Harness.test "a call through an alias of a function value counts as a call of it" (fun () ->
      expect_not_proven Fixtures.Prover.hits_through_an_alias_of_a_function_value "prover.cost");
  Harness.test "a match mut binding's new value is in the scrutinee after the arm" (fun () ->
      expect_proven Fixtures.Prover.match_mut_on_an_option_assigned)

let () =
  Harness.test "a function with a requires bound to a local must accept every argument" (fun () ->
      expect_codes Fixtures.Prover.below_three_bound_to_a_local
        [ "prover.requires"; "prover.requires" ]);
  Harness.test "a function with a requires passed through a local must accept every argument"
    (fun () ->
      expect_codes Fixtures.Prover.below_one_passed_through_a_local
        [ "prover.requires"; "prover.requires" ]);
  Harness.test "a callback's requires names a mut parameter as the caller passed it" (fun () ->
      expect_not_proven Fixtures.Prover.callback_requires_naming_a_mut_limit "prover.requires");
  Harness.test "a forwarded callback must be promised its requires" (fun () ->
      expect_not_proven Fixtures.Prover.callback_forwarded_without_its_requires "prover.requires");
  Harness.test "an impl's method proves the requires that its callback type states" (fun () ->
      expect_not_proven Fixtures.Prover.impl_calling_its_callback_outside_its_requires
        "prover.requires");
  Harness.test "a lambda passed to a trait's method relies on the callback type's requires"
    (fun () ->
      expect_proven Fixtures.Prover.lambda_relying_on_the_requires_of_a_trait_methods_callback);
  Harness.test "a forwarded callback with the callee's requires is accepted" (fun () ->
      expect_proven Fixtures.Prover.callback_forwarded_with_its_requires);
  Harness.test "a call through a function value gives a valid result" (fun () ->
      expect_proven Fixtures.Prover.positive_made_by_a_function_value);
  Harness.test "a lambda returns a valid value" (fun () ->
      expect_not_proven Fixtures.Prover.apply_of_a_positive_lambda "prover.invariant");
  Harness.test "a callback with a requires bound to a local must accept every argument" (fun () ->
      expect_codes Fixtures.Prover.callback_with_a_requires_bound_to_a_local
        [ "prover.requires"; "prover.requires" ])

let () =
  Harness.test "a callee relies on its callback type's ensures, which a lambda proves" (fun () ->
      expect_proven Fixtures.Prover.index_chosen_by_a_callback);
  Harness.test "a lambda must meet its callback type's ensures" (fun () ->
      expect_not_proven Fixtures.Prover.lambda_breaking_its_callback_ensures "prover.ensures");
  Harness.test "a named function's ensures must imply its callback type's" (fun () ->
      expect_not_proven Fixtures.Prover.named_function_breaking_its_callback_ensures
        "prover.ensures");
  Harness.test "a forwarded callback without a contract promises nothing of its results" (fun () ->
      expect_not_proven Fixtures.Prover.callback_forwarded_without_a_contract "prover.ensures");
  Harness.test "a forwarded callback keeps the contract its type states" (fun () ->
      expect_proven Fixtures.Prover.callback_forwarded_with_its_contract);
  Harness.test "a lambda passed to a trait's method must meet its callback type's ensures"
    (fun () ->
      expect_not_proven Fixtures.Prover.trait_method_lambda_breaking_its_callback_ensures
        "prover.ensures");
  Harness.test "a caller reads the postcondition of the function it passes from its body" (fun () ->
      expect_proven Fixtures.Prover.halved_through_a_callback_relation);
  Harness.test "a named function passed as a measure in a requires and an invariant proves"
    (fun () -> expect_proven Fixtures.Prover.zero_count_by_a_named_measure);
  Harness.test "a callback's mut input is related at its entry and its exit" (fun () ->
      expect_proven Fixtures.Prover.value_changed_through_a_mut_callback);
  Harness.test "two calls of an effectful callback are not known to agree" (fun () ->
      expect_not_proven Fixtures.Prover.two_random_results_claimed_equal "prover.ensures");
  Harness.test "a lambda knows that its argument is an element of the receiver" (fun () ->
      expect_proven Fixtures.Prover.doubled_elements_of_a_bounded_list);
  Harness.test "a comparator that keeps its laws gives max_by's conclusion" (fun () ->
      expect_proven Fixtures.Prover.largest_by_a_comparing_lambda);
  Harness.test "a comparator that breaks its laws gives max_by's conclusion nothing" (fun () ->
      expect_not_proven Fixtures.Prover.largest_by_a_comparator_breaking_its_laws "prover.ensures");
  Harness.test "a comparator that compares a field of its arguments gives max_by's conclusion"
    (fun () -> expect_proven Fixtures.Prover.highest_score_by_a_keyed_comparator);
  Harness.test "an element's range holds in a quantifier that is a match arm's value" (fun () ->
      expect_proven Fixtures.Prover.element_compared_in_a_match_arm)

let () =
  Harness.test "provided methods that call each other are recursion" (fun () ->
      expect_codes Fixtures.Prover.ping_and_pong_provided_methods
        [ "prover.termination"; "prover.termination" ]);
  Harness.test "an implementation that calls the function providing it is recursion" (fun () ->
      expect_codes Fixtures.Prover.looper_provided_by_its_own_caller
        [ "prover.termination"; "prover.termination" ])

let () =
  Harness.test "an impl's method that calls itself through its type is recursion" (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:
          "This recursive call may not end: give the function a `decreases` clause for the prover \
           to show that the recursion ends."
        Fixtures.Prover.from_calling_itself_through_its_type "prover.termination");
  Harness.test "an operator that calls its own method is recursion named by the operator" (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"The call to `Money.add` that `self + right` makes may not"
        Fixtures.Prover.money_adding_itself "prover.termination");
  Harness.test "a cursor's `next` that its own `for` loop calls is recursion named by the loop"
    (fun () ->
      Support.expect_one_diagnostic ~check ~at:("inner", 2)
        ~says:"The call to `Countdown.next` that this `for` loop makes may not"
        Fixtures.Prover.countdown_pulling_itself "prover.termination");
  Harness.test "an impl's method that calls itself through its receiver is recursion" (fun () ->
      expect_not_proven Fixtures.Prover.grow_calling_itself_through_its_receiver
        "prover.termination");
  Harness.test "an impl's method that calls itself through its trait is recursion" (fun () ->
      expect_not_proven Fixtures.Prover.grow_calling_itself_through_its_trait "prover.termination");
  Harness.test "methods of two impls that call each other without measures cannot be shown to end"
    (fun () ->
      match list_codes Fixtures.Prover.grow_of_two_impls_calling_each_other with
      | [ "prover.termination"; "prover.termination" ] -> ()
      | codes -> Harness.fail "codes %s" (String.concat ", " codes));
  Harness.test "methods of two impls that call each other with measures that decrease" (fun () ->
      expect_proven Fixtures.Prover.grow_of_two_impls_with_measures);
  Harness.test "a function that calls an impl's method that calls it back is recursion" (fun () ->
      Support.expect_one_diagnostic ~check ~at:("seed.grow(steps + 1)", 1)
        Fixtures.Prover.tend_calling_a_grow_that_calls_it_back "prover.termination");
  Harness.test "an impl's method whose measure decreases" (fun () ->
      expect_proven Fixtures.Prover.grow_with_a_measure_that_decreases);
  Harness.test "an impl's method whose measure does not decrease" (fun () ->
      expect_not_proven Fixtures.Prover.grow_with_a_measure_that_does_not_decrease
        "prover.termination");
  Harness.test "an impl's method that recurses on a part of its receiver ends" (fun () ->
      expect_proven (tree ^ Fixtures.Prover.depth_of_a_tree_in_an_impl));
  Harness.test "an impl's method that recurses on an element of a field's list ends" (fun () ->
      expect_proven Fixtures.Prover.tree_visit_of_its_children_in_an_impl);
  Harness.test "an impl's method that recurses on its receiver itself does not end" (fun () ->
      expect_not_proven
        (tree ^ Fixtures.Prover.depth_of_the_tree_itself_in_an_impl)
        "prover.termination");
  Harness.test "an override that calls another type's provided method is not recursion" (fun () ->
      expect_proven Fixtures.Prover.describe_overridden_by_calling_a_provided_describe);
  Harness.test "a written method that calls a derived method of its trait is not recursion"
    (fun () -> expect_proven Fixtures.Prover.default_written_over_a_derived_default);
  Harness.test
    "a written method that calls a written method that calls a derived method of their trait is \
     not recursion" (fun () ->
      expect_proven Fixtures.Prover.default_written_over_a_written_default_over_a_derived_default);
  Harness.test "a written method that calls an integer's inherited max is not recursion" (fun () ->
      expect_proven Fixtures.Prover.rank_compare_calling_the_max_of_an_integer);
  Harness.test "a written equal that gives a derived Equal to a generic function is not recursion"
    (fun () ->
      expect_proven Fixtures.Prover.outer_equal_through_a_generic_function_given_a_derived_equal);
  Harness.test "an override that calls provided methods that its impl inherits is not recursion"
    (fun () -> expect_proven Fixtures.Prover.clamp_overridden_by_calling_inherited_max_and_min);
  Harness.test "provided methods that call each other with measures that decrease" (fun () ->
      expect_proven Fixtures.Prover.ping_and_pong_provided_with_measures);
  Harness.test "an impl's method that may run forever calls itself without a measure" (fun () ->
      expect_proven Fixtures.Prover.grow_that_may_run_forever_calling_itself_through_its_receiver);
  Harness.test "an impl's method's written measure holds where the method may run forever"
    (fun () ->
      Support.expect_one_diagnostic ~check ~says:"This call may not decrease `steps`."
        Fixtures.Prover.grow_that_may_run_forever_with_a_measure_that_does_not_decrease
        "prover.termination");
  Harness.test
    "a recursion through an impl given to a bound is not rejected where its methods may run forever"
    (fun () ->
      expect_proven Fixtures.Prover.pot_that_may_run_forever_growing_a_seed_that_grows_a_pot);
  Harness.test
    "a recursion through an inherited method is not rejected where the methods may run forever"
    (fun () ->
      expect_proven
        Fixtures.Prover.pong_that_may_run_forever_calling_an_inherited_ping_that_calls_it_back)

let () =
  Harness.test "a call of an inherited method that calls back is recursion through inherited code"
    (fun () ->
      Support.expect_one_diagnostic ~check ~says:"through code that its `impl` inherits"
        ~at:("Foo().ping(steps)", 1) Fixtures.Prover.poke_calling_a_provided_ping_that_calls_it_back
        "prover.termination");
  Harness.test
    "a written method and a method its impl inherits that call each other are recursion through \
     inherited code" (fun () ->
      Support.expect_one_diagnostic ~check ~says:"through code that its `impl` inherits"
        ~at:("self.ping(steps - 1)", 1)
        Fixtures.Prover.pong_calling_an_inherited_ping_that_calls_it_back "prover.termination");
  Harness.test "a provided body that calls itself on a type is recursion through inherited code"
    (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:
          "This call to `Hop.step` reaches back here through code that its `impl` inherits from \
           its trait. No measure can be stated for that code, so the recursion cannot be shown to \
           end."
        Fixtures.Prover.step_provided_by_calling_itself_on_a_type "prover.termination");
  Harness.test
    "a provided body that gives its receiver to a generic function that calls it back is recursion"
    (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"This call uses `app.main.Step` where a bound needs it, and its methods reach back"
        ~at:("run(self)", 1)
        Fixtures.Prover.step_provided_by_giving_its_receiver_to_a_generic_function
        "prover.termination");
  Harness.test "a call of a derived method that calls back is recursion through derived code"
    (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:
          "This call to `Holder.default` reaches back here through code that its `impl` derives. \
           No measure can be stated for that code, so the recursion cannot be shown to end."
        Fixtures.Prover.default_calling_a_derived_default_that_calls_it_back "prover.termination");
  Harness.test "an equal that compares its receiver with the operator is recursion" (fun () ->
      expect_one_termination_failure ~says:"give the function a `decreases` clause"
        Fixtures.Prover.equal_comparing_its_receiver_with_the_operator);
  Harness.test "an equal that compares its receiver in a derived wrapper is recursion" (fun () ->
      expect_one_termination_failure ~says:"through code that its `impl` derives"
        Fixtures.Prover.equal_comparing_its_receiver_through_a_derived_wrapper);
  Harness.test "an equal that compares lists of its own type gives its impl to the list's equal"
    (fun () ->
      expect_one_termination_failure
        ~says:
          "The call that `self.children == other.children` makes uses `app.main.impl \
           standard.core.Equal for app.main.Tree` where a bound needs it, and its methods reach \
           back here."
        Fixtures.Prover.tree_equal_comparing_its_lists_of_children);
  Harness.test "an equal that compares each child in a loop recurses on parts" (fun () ->
      match list_termination_messages Fixtures.Prover.tree_equal_comparing_each_child with
      | [] -> ()
      | messages -> Harness.fail "%s" (String.concat "; " messages));
  Harness.test "a method of a generic impl is given the impl of its type argument" (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"uses `app.main.impl app.main.Grow for app.main.Seed` where a bound needs it"
        Fixtures.Prover.pot_growing_a_seed_that_grows_a_pot "prover.termination");
  Harness.test "a derived method of a generic type is given the impl of its type argument"
    (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"uses `app.main.impl standard.core.Default for app.main.Seed` where a bound needs it"
        Fixtures.Prover.default_of_a_seed_through_a_derived_default_of_its_pot "prover.termination");
  Harness.test "a trait's method is given the impls of its own type arguments" (fun () ->
      Support.expect_one_diagnostic ~check
        ~says:"uses `app.main.impl app.main.Grow for app.main.Seed` where a bound needs it"
        Fixtures.Prover.visit_given_a_seed_that_calls_it_back "prover.termination")

let () =
  Harness.test "a constant's value is well defined" (fun () ->
      expect_not_proven "let shifted: UInt8 = 1 << 8\n" "prover.shift");
  Harness.test "a constant whose value is in range proves" (fun () ->
      expect_proven "let shifted: UInt8 = 1 << 7\n")

let () =
  Harness.test "generic negation without `Panic` proves the trait method's condition" (fun () ->
      expect_not_proven Fixtures.Prover.generic_negation "prover.panic"
        ~fixed:
          ( "fn negate[Number: Negate](value: Number) -> Number.Output {",
            "fn negate[Number: Negate](value: Number) -> Number.Output\n\
            \  requires value.negate_is_defined()\n\
             {" )
        ~alternatives:
          [
            ( "fn negate[Number: Negate](value: Number) -> Number.Output {",
              "fn negate[Number: Negate](value: Number) -> Number.Output\n  uses Panic\n{" );
          ]);
  Harness.test "generic negation proves where the trait method's condition holds" (fun () ->
      expect_proven Fixtures.Prover.generic_negation_with_its_precondition);
  Harness.test
    "a function with a time clause converts, makes a default, and indexes through a bound"
    (fun () ->
      expect_proven Fixtures.Prover.conversions_and_indexing_through_bounds_under_a_time_clause)

let () =
  Harness.test "a float converted to an integer keeps the bounds checked on the float" (fun () ->
      expect_proven Fixtures.Prover.float_converted_within_bounds_on_the_float);
  Harness.test "a float with a fraction does not convert to an integer" (fun () ->
      expect_proven Fixtures.Prover.float_with_a_fraction_not_converted);
  Harness.test "the least Int64 converts from a float and the next power of two does not" (fun () ->
      expect_proven Fixtures.Prover.float_converted_at_the_limits_of_int64);
  Harness.test "a character converts from its scalar code and back" (fun () ->
      expect_proven Fixtures.Prover.character_converted_from_a_scalar_code);
  Harness.test "an integer converted to a BigInteger converts back to itself" (fun () ->
      expect_proven Fixtures.Prover.big_integer_converted_back)

let () =
  Harness.test "two literals with the same text are the same value" (fun () ->
      expect_proven Fixtures.Prover.literal_ensured_identical_to_itself);
  Harness.test "two literals with different text are different values" (fun () ->
      expect_not_proven Fixtures.Prover.literal_ensured_identical_to_another "prover.ensures");
  Harness.test "a map built with a literal key contains the same literal" (fun () ->
      expect_proven Fixtures.Prover.map_built_with_a_literal_key)

let () =
  Harness.test "a bit set below a symbolic width keeps the bits above it clear" (fun () ->
      expect_proven Fixtures.Prover.bit_written_below_a_symbolic_width);
  Harness.test "an exclusive or may be below its first operand" (fun () ->
      expect_not_proven Fixtures.Prover.exclusive_or_ensured_at_least_its_first "prover.ensures")

let () =
  Harness.test "a derived ordering is the one a law of another trait reads" (fun () ->
      expect_proven Fixtures.Prover.day_ordering_read_by_a_law)

let () =
  Harness.test "a derived equality compares a list field as the list's equal does" (fun () ->
      expect_proven Fixtures.Prover.limbs_equality);
  Harness.test "a law reads an impl of Equal whose bounds hold in the impl it is proven for"
    (fun () -> expect_proven Fixtures.Prover.named_law_reading_equal)

let () =
  Harness.test "a deque's potential pays for moving half of one list to the other" (fun () ->
      expect_proven Fixtures.Prover.deque_with_potential);
  Harness.test "a copy pays for the potential it makes" (fun () ->
      expect_proven Fixtures.Prover.push_copy);
  Harness.test "a loop of pushed copies is amortized over the copies' time" (fun () ->
      expect_proven Fixtures.Prover.append_copies)

let () =
  Harness.test
    "a loop that pushes a callback's values of a type parameter costs the callback's time"
    (fun () -> expect_proven Fixtures.Prover.loop_pushing_values_of_a_type_parameter);
  Harness.test "a loop that moves a cursor's values of a type parameter into a list is linear"
    (fun () -> expect_proven Fixtures.Prover.loop_moving_values_of_a_type_parameter);
  Harness.test "a loop that pushes lists of unknown length is linear in its iterations" (fun () ->
      expect_proven Fixtures.Prover.loop_pushing_lists_of_unknown_length);
  Harness.test "a loop that pushes a callback's values spends the callback's time in each iteration"
    (fun () ->
      expect_codes Fixtures.Prover.loop_pushing_values_of_a_type_parameter_with_a_small_cost_clause
        [ "prover.cost"; "prover.cost" ]);
  Harness.test "a function that pushes a callback's values in a loop spends the loop's cost"
    (fun () ->
      expect_not_proven Fixtures.Prover.loop_pushing_values_of_a_type_parameter_within_a_small_bound
        "prover.cost");
  Harness.test
    "an amortized push onto a list that a callback returned pays for the list's potential"
    (fun () ->
      expect_not_proven Fixtures.Prover.amortized_push_onto_a_list_that_a_callback_returns
        "prover.cost");
  Harness.test "a push onto a list that a callback returned spends the list's potential" (fun () ->
      expect_not_proven Fixtures.Prover.loop_pushing_onto_a_list_that_a_callback_returns
        "prover.cost");
  Harness.test "a loop that pushes the values of a callback's options costs the callback's time"
    (fun () -> expect_proven Fixtures.Prover.loop_pushing_the_values_of_a_callbacks_options);
  Harness.test "a loop that appends a callback's lists costs their lengths and the callback's time"
    (fun () -> expect_proven Fixtures.Prover.loop_appending_lists_that_a_callback_returns);
  Harness.test "a cost bound may call a method of the result, whose invariant holds" (fun () ->
      expect_proven Fixtures.Prover.cost_bound_reading_a_method_of_the_result);
  Harness.test "a loop that appends a callback's lists spends their lengths" (fun () ->
      expect_not_proven
        Fixtures.Prover.loop_appending_lists_that_a_callback_returns_without_their_lengths
        "prover.cost");
  Harness.test "nested loops that push lists of unknown length cost their iterations" (fun () ->
      expect_proven Fixtures.Prover.nested_loops_pushing_lists_of_unknown_length);
  Harness.test "an amortized bound pays for the potential of the values a loop pushes" (fun () ->
      expect_not_proven Fixtures.Prover.amortized_loop_pushing_values_of_a_type_parameter
        "prover.cost");
  Harness.test "an amortized bound covers the potential of the lists a loop pushes" (fun () ->
      expect_proven Fixtures.Prover.amortized_loop_pushing_lists_of_known_length);
  Harness.test
    "a loop without a cost clause that pushes a callback's values costs the callback's time"
    (fun () ->
      expect_proven Fixtures.Prover.loop_pushing_values_of_a_type_parameter_without_a_cost_clause);
  Harness.test "a loop without a cost clause that moves a cursor's values into a list is linear"
    (fun () ->
      expect_proven Fixtures.Prover.loop_moving_values_of_a_type_parameter_without_a_cost_clause);
  Harness.test
    "a loop without a cost clause that pushes onto a list a callback returned spends its potential"
    (fun () ->
      expect_not_proven
        Fixtures.Prover.loop_pushing_onto_a_list_that_a_callback_returns_without_a_cost_clause
        "prover.cost");
  Harness.test
    "a loop without a cost clause around one that pushes lists costs both loops' iterations"
    (fun () ->
      expect_proven Fixtures.Prover.unstated_loop_around_a_loop_pushing_lists_of_unknown_length);
  Harness.test
    "a loop's cost clause holds where a callee with only an amortized bound pops its list"
    (fun () ->
      expect_proven Fixtures.Prover.loop_popping_through_a_callee_with_only_an_amortized_bound);
  Harness.test "a loop's cost clause holds where a branch pops its list through such a callee"
    (fun () ->
      expect_proven
        Fixtures.Prover.loop_popping_in_a_branch_through_a_callee_with_only_an_amortized_bound)

let check_across library program =
  let packages =
    Support.setup
      ~dependencies:[ ("app", "lib") ]
      [ ("lib.numbers", library); ("app.main", "use lib.numbers\n\n" ^ program) ]
  in
  check packages (Support.parse_file "app.main")

let public_doubling =
  "public fn double(limit_count: Int64) -> Int64\n\
  \  requires limit_count < 1000 && limit_count > -1000\n\
  \  ensures result == limit_count * 2\n\
  \  cost time O(1)\n\
   {\n\
  \  limit_count * 2\n\
   }\n"

let () =
  Harness.test "another package does not assume an opaque type's invariant" (fun () ->
      match
        check_across Fixtures.Prover.public_counter_with_an_invariant
          Fixtures.Prover.value_bounded_by_another_packages_invariant
      with
      | [ { code; _ } ] when Diagnostic.Code.name code = "prover.ensures" -> ()
      | actual -> Harness.fail "%s" (String.concat "; " (Support.list_codes actual)))

let () =
  Harness.test "a caller in another package reads its callee's contract" (fun () ->
      match check_across public_doubling Fixtures.Prover.twice_through_another_packages_double with
      | [] -> ()
      | actual ->
          Harness.fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
  Harness.test
    "a proof in another package does not know the fields of an evaluated constant of an opaque type"
    (fun () ->
      let token =
        "public opaque type Token(code: UInt64)\n\n\
         fn make_token() -> Token {\n\
        \  Token(code: 7)\n\
         }\n\n\
         public let token: Token = make_token()\n\n\
         public fn Token.read_code(self) -> UInt64 {\n\
        \  self.code\n\
         }\n"
      in
      (match
         Support.list_codes
           (check_across token
              "fn f() -> UInt64\n  ensures result == 7\n{\n  numbers.token.read_code()\n}\n")
       with
      | [ "prover.ensures" ] -> ()
      | codes -> Harness.fail "codes [%s]" (String.concat "; " codes));
      expect_proven (token ^ "\nfn inside() -> UInt64\n  ensures result == 7\n{\n  token.code\n}\n"));
  Harness.test
    "a caller of another package's function that passes a derived impl where a bound needs one is \
     proven" (fun () ->
      match
        Support.list_codes
          (check_across Fixtures.Prover.public_same_versions_of_a_derived_version
             Fixtures.Prover.same_versions_of_a_dependency_ensured_false)
      with
      | [ "prover.ensures" ] -> ()
      | codes -> Harness.fail "codes %s" (String.concat ", " codes));
  Harness.test
    "the time of a bound's method is the time that an impl states in the package of its trait"
    (fun () ->
      match
        Support.list_codes
          (check_across Fixtures.Prover.public_weighed_with_an_impl_for_uint64
             Fixtures.Prover.weigh_of_a_uint64_in_constant_time)
      with
      | [] -> ()
      | codes -> Harness.fail "codes %s" (String.concat ", " codes))

let expect_a_message_saying ~says diagnostics =
  let messages = List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) diagnostics in
  if not (List.exists (String.includes ~affix:says) messages) then
    Harness.fail "no message says %S: %s" says (String.concat "; " messages)

let () =
  Harness.test "a loop that calls a function with no cost clause names the function" (fun () ->
      expect_a_message_saying
        ~says:
          "This loop calls `is_even`, which states no `cost time`, so the prover cannot bound the \
           cost of an iteration. Give `is_even` a `cost time` clause, such as `cost time O(1)`."
        (list_diagnostics Fixtures.Prover.loop_calling_a_helper_without_a_cost_clause));
  Harness.test "a loop that calls functions with no cost clauses names each of them" (fun () ->
      expect_a_message_saying
        ~says:
          "This loop calls `is_even` and `is_negative`, which state no `cost time`, so the prover \
           cannot bound the cost of an iteration. Give each a `cost time` clause, such as `cost \
           time O(1)`."
        (list_diagnostics Fixtures.Prover.loop_calling_helpers_without_cost_clauses));
  Harness.test "a loop's cost is counted once the function it calls states a cost" (fun () ->
      expect_proven Fixtures.Prover.loop_calling_a_helper_with_a_cost_clause);
  Harness.test
    "a loop that calls another package's function with no cost clause asks no change of it"
    (fun () ->
      let diagnostics =
        check_across Fixtures.Prover.public_is_even_without_a_cost_clause
          Fixtures.Prover.loop_calling_another_packages_function_without_a_cost_clause
      in
      expect_a_message_saying
        ~says:
          "This loop calls `is_even`, which states no `cost time`, so the prover cannot bound the \
           cost of an iteration."
        diagnostics;
      if
        List.exists
          (fun (diagnostic : Diagnostic.t) -> String.includes ~affix:"Give" diagnostic.message)
          diagnostics
      then Harness.fail "a message asks for a change to another package");
  Harness.test "a loop that pushes on one path is amortized linear" (fun () ->
      expect_proven Fixtures.Prover.loop_pushing_in_one_branch);
  Harness.test "a loop that pushes on one path onto a fresh list is linear" (fun () ->
      expect_proven Fixtures.Prover.loop_pushing_in_one_branch_within_a_plain_bound);
  Harness.test "a loop that pushes on one path onto a `mut` parameter is amortized linear"
    (fun () -> expect_proven Fixtures.Prover.loop_pushing_onto_a_parameter_in_one_branch);
  Harness.test "a loop that pushes on one path is counted by its cost clause" (fun () ->
      expect_proven Fixtures.Prover.loop_pushing_in_one_branch_with_a_cost_clause);
  Harness.test "an amortized loop names a mutating callee that states no amortized bound" (fun () ->
      expect_a_message_saying
        ~says:
          "`drop_last` states no `cost amortized time`, so the prover counts `drop_last(mut kept)` \
           at its plain cost plus the change in potential of the values it mutates or returns. The \
           prover cannot bound that change by the values this loop does not mutate. Give \
           `drop_last` a `cost amortized time` clause."
        (list_diagnostics Fixtures.Prover.loop_calling_a_mutating_callee_without_an_amortized_bound))

let () =
  Harness.test
    "a recursive function proves a plain and an amortized bound, each by its own counting"
    (fun () -> expect_proven Fixtures.Prover.shift_left_all)

let () =
  Harness.test "a callee's clause in another file is named by its file and line" (fun () ->
      let actual = read_message Fixtures.Prover.swap_in_a_list_that_may_be_empty in
      if
        not
          (String.includes ~affix:"The clause that must hold is at `standard/list/elements.truss:"
             actual)
      then Harness.fail "message %S" actual)

let () =
  Harness.test "an insertion into a set of integers is amortized in the logarithm of its length"
    (fun () -> expect_proven Fixtures.Prover.integer_set_add);
  Harness.test
    "an insertion into a set of any elements is amortized in a hash and a logarithm of comparisons"
    (fun () -> expect_proven Fixtures.Prover.generic_set_add);
  Harness.test "a list filled with integers is linear in its count" (fun () ->
      expect_proven Fixtures.Prover.zeros_filled)

let () =
  Harness.test "a requires fix reads a negated negation as the value it negates" (fun () ->
      let text = Fixtures.Prover.negation_of_a_negated_parameter in
      let packages = Support.setup [ ("app.main", text) ] in
      match check packages (Support.parse_file "app.main") with
      | [ { fixes = [ fix; { title = "Add `uses Panic`"; _ } ]; _ } ] ->
          if fix.title <> "Add `requires value <= Int64.maximum - 1`" then
            Harness.fail "%s" fix.title;
          expect_proven (Diagnostic.apply_edits text fix.edits)
      | actual -> Harness.fail "%d diagnostics" (List.length actual))

let () =
  Harness.test "a callee's requires about the caller's parameters is offered as the caller's"
    (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Prover.halve_of_an_unbounded_parameter) ]
      in
      match check packages (Support.parse_file "app.main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count < 100`" -> ()
      | actual ->
          Harness.fail "%s"
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    String.concat ", "
                      (List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes))
                  actual)))

let () =
  Harness.test "a fact made in a quantifier's body is a hypothesis of the goal" (fun () ->
      expect_proven Fixtures.Prover.count_ones_at_most_32_for_each);
  Harness.test "a bitwise operation under a quantifier is defined for each bound value" (fun () ->
      expect_proven Fixtures.Prover.low_byte_of_each_element);
  Harness.test "a fact made in a quantifier's body proves nothing false" (fun () ->
      expect_not_proven Fixtures.Prover.count_ones_at_most_31_for_each "prover.ensures")

let () =
  Harness.test "a callee's ensures under its requires holds for every bound value" (fun () ->
      expect_proven Fixtures.Prover.counted_up_under_a_quantifier);
  Harness.test "a theorem called in a quantifier's body proves its fact for every bound value"
    (fun () -> expect_proven Fixtures.Prover.sorted_prefix_through_a_theorem);
  Harness.test "a theorem called in a quantifier's body needs its requires for every bound value"
    (fun () ->
      expect_not_proven Fixtures.Prover.theorem_under_a_quantifier_without_its_requires
        "prover.requires")

let () =
  Harness.test "a value returned from a concurrent block is the winning branch's" (fun () ->
      expect_proven Fixtures.Prover.value_returned_from_a_concurrent_branch);
  Harness.test "a concurrent for may return early, with a value known by its type" (fun () ->
      expect_proven Fixtures.Prover.any_negative_through_a_concurrent_for);
  Harness.test "a value returned from a concurrent for is not known to be any one iteration's"
    (fun () -> expect_not_proven Fixtures.Prover.claimed_through_a_concurrent_for "prover.ensures");
  Harness.test "a function that waits for its tasks has no time bound" (fun () ->
      expect_not_proven Fixtures.Prover.concurrent_block_under_a_time_bound "prover.cost";
      expect_not_proven Fixtures.Prover.concurrent_for_under_a_time_bound "prover.cost");
  Harness.test "waiting for tasks allocates nothing" (fun () ->
      expect_proven Fixtures.Prover.concurrent_block_under_an_allocation_bound)

let () =
  Harness.test "an impl's method offers no requires, since the trait's would have to imply it"
    (fun () ->
      expect_not_proven Fixtures.Prover.increment_in_a_describe_impl "prover.overflow";
      expect_not_proven Fixtures.Prover.increment_in_a_greeter_impl "prover.overflow";
      expect_not_proven Fixtures.Prover.decrement_in_a_countdown_cursor "prover.overflow");
  Harness.test "a narrowing conversion names its callee and offers each bound at the target"
    (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Prover.integer_narrowed_without_a_check) ]
      in
      let describe (diagnostic : Diagnostic.t) =
        ( String.includes ~affix:"for this call to `Int8.from_integer`" diagnostic.message,
          List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes )
      in
      match check packages (Support.parse_file "app.main") with
      | actual
        when List.sort compare (List.map describe actual)
             = [
                 (true, [ "Add `requires Int8.minimum_value() <= value`"; "Add `uses Panic`" ]);
                 (true, [ "Add `requires value <= Int8.maximum_value()`"; "Add `uses Panic`" ]);
               ] ->
          ()
      | actual ->
          Harness.fail "%s"
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    String.concat ", "
                      (diagnostic.message
                      :: List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes))
                  actual)));
  Harness.test "a divisor that may be zero offers a requires that it is not" (fun () ->
      expect_not_proven Fixtures.Prover.halves_of_an_unchecked_divisor "prover.division"
        ~fixed:
          ( "fn halves(total: UInt32, parts: UInt32) -> UInt32 {",
            "fn halves(total: UInt32, parts: UInt32) -> UInt32\n  requires parts != 0\n{" )
        ~alternatives:
          [
            ( "fn halves(total: UInt32, parts: UInt32) -> UInt32 {",
              "fn halves(total: UInt32, parts: UInt32) -> UInt32\n  uses Panic\n{" );
          ]);
  Harness.test "a shift amount that may be too large offers a requires below the width" (fun () ->
      expect_not_proven Fixtures.Prover.shifted_by_an_unbounded_amount "prover.shift"
        ~fixed:
          ( "fn shifted(value: UInt64, by: UInt64) -> UInt64 {",
            "fn shifted(value: UInt64, by: UInt64) -> UInt64\n  requires by < 64\n{" )
        ~alternatives:
          [
            ( "fn shifted(value: UInt64, by: UInt64) -> UInt64 {",
              "fn shifted(value: UInt64, by: UInt64) -> UInt64\n  uses Panic\n{" );
          ]);
  Harness.test "an overflow with a literal offers the bound as a requires" (fun () ->
      expect_not_proven Fixtures.Prover.next_count "prover.overflow"
        ~fixed:
          ( "fn next(count: UInt8) -> UInt8 {",
            "fn next(count: UInt8) -> UInt8\n  requires count <= UInt8.maximum - 1\n{" )
        ~alternatives:
          [
            ("fn next(count: UInt8) -> UInt8 {", "fn next(count: UInt8) -> UInt8\n  uses Panic\n{");
          ]);
  Harness.test "a failed assert about the parameters offers it as a requires" (fun () ->
      expect_not_proven Fixtures.Prover.assert_on_ordered_parameters "prover.assertion"
        ~fixed:
          ( "fn ordered(low: Int64, high: Int64) -> Int64 {",
            "fn ordered(low: Int64, high: Int64) -> Int64\n  requires low < high\n{" ));
  Harness.test "a failed assert under an if offers the if's condition as a premise" (fun () ->
      expect_not_proven Fixtures.Prover.assert_under_an_if "prover.assertion"
        ~fixed:
          ( "fn guarded(flag: Bool, count: Int64) -> Int64 {",
            "fn guarded(flag: Bool, count: Int64) -> Int64\n  requires (flag) ==> (count > 0)\n{" ));
  Harness.test "a failed assert with arithmetic offers it as a requires" (fun () ->
      expect_not_proven Fixtures.Prover.assert_on_spaced_parameters "prover.assertion"
        ~fixed:
          ( "fn spaced(low: Int64, high: Int64) -> Int64 {",
            "fn spaced(low: Int64, high: Int64) -> Int64\n\
            \  requires low + 2 * high <= 100 - (high - low)\n\
             {" ));
  Harness.test "an overflow of a local offers the bound on the parameter it holds" (fun () ->
      expect_not_proven Fixtures.Prover.bumped_local "prover.overflow"
        ~fixed:
          ( "fn bumped(start: Int64) -> Int64 {",
            "fn bumped(start: Int64) -> Int64\n  requires start <= Int64.maximum - 1\n{" )
        ~alternatives:
          [
            ( "fn bumped(start: Int64) -> Int64 {",
              "fn bumped(start: Int64) -> Int64\n  uses Panic\n{" );
          ]);
  Harness.test "a callee's requires through a local names the caller's parameter" (fun () ->
      expect_not_proven Fixtures.Prover.halve_of_a_local "prover.requires"
        ~fixed:
          ( "fn quarter(total: UInt32) -> UInt32 {",
            "fn quarter(total: UInt32) -> UInt32\n  requires total < 100\n{" ));
  Harness.test "an unsigned sum that may overflow offers only its upper bound" (fun () ->
      expect_not_proven Fixtures.Prover.total_of_two_bytes "prover.overflow"
        ~fixed:
          ( "fn total(count: UInt8, other: UInt8) -> UInt8 {",
            "fn total(count: UInt8, other: UInt8) -> UInt8\n\
            \  requires count + other <= UInt8.maximum\n\
             {" )
        ~alternatives:
          [
            ( "fn total(count: UInt8, other: UInt8) -> UInt8 {",
              "fn total(count: UInt8, other: UInt8) -> UInt8\n  uses Panic\n{" );
          ]);
  Harness.test "an unsigned difference that may overflow offers only its lower bound" (fun () ->
      expect_not_proven Fixtures.Prover.gap "prover.overflow"
        ~fixed:
          ( "fn gap(low: UInt8, high: UInt8) -> UInt8 {",
            "fn gap(low: UInt8, high: UInt8) -> UInt8\n  requires 0 <= high - low\n{" )
        ~alternatives:
          [
            ( "fn gap(low: UInt8, high: UInt8) -> UInt8 {",
              "fn gap(low: UInt8, high: UInt8) -> UInt8\n  uses Panic\n{" );
          ]);
  Harness.test "a signed product that may overflow offers both limits by name" (fun () ->
      expect_not_proven Fixtures.Prover.scaled_count "prover.overflow"
        ~fixed:
          ( "fn scaled(count: Int64) -> Int64 {",
            "fn scaled(count: Int64) -> Int64\n\
            \  requires Int64.minimum <= count * 1000 && count * 1000 <= Int64.maximum\n\
             {" )
        ~alternatives:
          [
            ( "fn scaled(count: Int64) -> Int64 {",
              "fn scaled(count: Int64) -> Int64\n  uses Panic\n{" );
          ]);
  Harness.test "an overflow under an if offers the if's condition as a premise" (fun () ->
      expect_not_proven Fixtures.Prover.product_under_an_if "prover.overflow"
        ~fixed:
          ( "fn product(flag: Bool, left: Int64, right: Int64) -> Int64 {",
            "fn product(flag: Bool, left: Int64, right: Int64) -> Int64\n\
            \  requires (flag) ==> (Int64.minimum <= left * right && left * right <= Int64.maximum)\n\
             {" )
        ~alternatives:
          [
            ( "fn product(flag: Bool, left: Int64, right: Int64) -> Int64 {",
              "fn product(flag: Bool, left: Int64, right: Int64) -> Int64\n  uses Panic\n{" );
          ]);
  Harness.test "a negation that may overflow offers to exclude the least value" (fun () ->
      expect_not_proven Fixtures.Prover.negated_value "prover.overflow"
        ~fixed:
          ( "fn negated(value: Int64) -> Int64 {",
            "fn negated(value: Int64) -> Int64\n  requires value != Int64.minimum\n{" )
        ~alternatives:
          [
            ( "fn negated(value: Int64) -> Int64 {",
              "fn negated(value: Int64) -> Int64\n  uses Panic\n{" );
          ]);
  Harness.test "a signed quotient that may overflow offers to exclude the least value over -1"
    (fun () ->
      expect_not_proven Fixtures.Prover.signed_quotient "prover.overflow"
        ~fixed:
          ( "requires divisor != 0\n{\n  dividend / divisor",
            "requires divisor != 0\n\
            \  requires dividend != Int64.minimum || divisor != -1\n\
             {\n\
            \  dividend / divisor" )
        ~alternatives:[ ("requires divisor != 0", "uses Panic\n  requires divisor != 0") ]);
  Harness.test "an overflow with a literal under an if offers the if's condition as a premise"
    (fun () ->
      expect_not_proven Fixtures.Prover.next_count_under_an_if "prover.overflow"
        ~fixed:
          ( "fn next(flag: Bool, count: UInt8) -> UInt8 {",
            "fn next(flag: Bool, count: UInt8) -> UInt8\n\
            \  requires (flag) ==> (count <= UInt8.maximum - 1)\n\
             {" )
        ~alternatives:
          [
            ( "fn next(flag: Bool, count: UInt8) -> UInt8 {",
              "fn next(flag: Bool, count: UInt8) -> UInt8\n  uses Panic\n{" );
          ]);
  Harness.test "a divisor under an if offers the if's condition as a premise" (fun () ->
      expect_not_proven Fixtures.Prover.divisor_under_an_if "prover.division"
        ~fixed:
          ( "fn halves(flag: Bool, total: UInt32, parts: UInt32) -> UInt32 {",
            "fn halves(flag: Bool, total: UInt32, parts: UInt32) -> UInt32\n\
            \  requires (flag) ==> (parts != 0)\n\
             {" )
        ~alternatives:
          [
            ( "fn halves(flag: Bool, total: UInt32, parts: UInt32) -> UInt32 {",
              "fn halves(flag: Bool, total: UInt32, parts: UInt32) -> UInt32\n  uses Panic\n{" );
          ]);
  Harness.test "a shift amount under an if offers the if's condition as a premise" (fun () ->
      expect_not_proven Fixtures.Prover.shift_under_an_if "prover.shift"
        ~fixed:
          ( "fn shifted(flag: Bool, value: UInt64, by: UInt64) -> UInt64 {",
            "fn shifted(flag: Bool, value: UInt64, by: UInt64) -> UInt64\n\
            \  requires (flag) ==> (by < 64)\n\
             {" )
        ~alternatives:
          [
            ( "fn shifted(flag: Bool, value: UInt64, by: UInt64) -> UInt64 {",
              "fn shifted(flag: Bool, value: UInt64, by: UInt64) -> UInt64\n  uses Panic\n{" );
          ]);
  Harness.test "a callee's requires under an if offers the if's condition as a premise" (fun () ->
      expect_not_proven Fixtures.Prover.call_under_an_if "prover.requires"
        ~fixed:
          ( "fn quarter(flag: Bool, count: UInt32) -> UInt32 {",
            "fn quarter(flag: Bool, count: UInt32) -> UInt32\n\
            \  requires (flag) ==> (count < 100)\n\
             {" ));
  Harness.test "a condition with no spelling in the parameters leaves the requires unconditional"
    (fun () ->
      expect_not_proven Fixtures.Prover.next_count_under_a_quotient "prover.overflow"
        ~fixed:
          ( "fn next(count: UInt8) -> UInt8 {",
            "fn next(count: UInt8) -> UInt8\n  requires count <= UInt8.maximum - 1\n{" )
        ~alternatives:
          [
            ("fn next(count: UInt8) -> UInt8 {", "fn next(count: UInt8) -> UInt8\n  uses Panic\n{");
          ]);
  Harness.test "a failed assert about a call's result offers no requires" (fun () ->
      expect_not_proven Fixtures.Prover.assert_on_a_list_length "prover.assertion");
  Harness.test "an overflow names the fixes that change the code's semantics" (fun () ->
      let actual = read_message Fixtures.Prover.next_count in
      if not (String.includes ~affix:"checked operation" actual) then
        Harness.fail "message %S" actual)

let () =
  let read_span text (span : Source.span) = String.sub text span.start (span.stop - span.start) in
  let list_failures text =
    List.map
      (fun ({ code; span; notes; _ } : Diagnostic.t) ->
        ( Diagnostic.Code.name code,
          read_span text span,
          List.map (fun (cited, _) -> read_span text cited) notes ))
      (list_diagnostics text)
  in
  let show_failures failures =
    String.concat "; "
      (List.map
         (fun (code, shown, cited) ->
           Printf.sprintf "%s at `%s` citing [%s]" code shown (String.concat ", " cited))
         failures)
  in
  Harness.test "an ensures that an early return breaks is reported at the `?` that returns"
    (fun () ->
      match list_failures Fixtures.Prover.checked_through_two_tries with
      | [ ("prover.ensures", "check_even(low)?", [ "result.is_ok()" ]) ] -> ()
      | failures -> Harness.fail "%s" (show_failures failures));
  Harness.test "an ensures that the `else` of a `let ... else` breaks is reported at its `return`"
    (fun () ->
      match list_failures Fixtures.Prover.found_or_zero with
      | [ ("prover.ensures", "return 0", [ "result > 0" ]) ] -> ()
      | failures -> Harness.fail "%s" (show_failures failures));
  let expect_message_saying text says =
    let actual = read_message text in
    if not (String.includes ~affix:says actual) then Harness.fail "message %S" actual
  in
  let expect_messages_saying text expected =
    let packages = Support.setup [ ("app.main", text) ] in
    let messages =
      List.map
        (fun (diagnostic : Diagnostic.t) -> diagnostic.message)
        (check packages (Support.parse_file "app.main"))
    in
    List.iter
      (fun says ->
        if not (List.exists (String.includes ~affix:says) messages) then
          Harness.fail "no message says %S: %s" says (String.concat "; " messages))
      expected
  in
  let impl_precondition = "may not follow from the trait's precondition" in
  Harness.test "a precondition of a `for` loop's call names the loop" (fun () ->
      expect_messages_saying Fixtures.Prover.sum_over_a_short_bag
        [
          impl_precondition;
          "may not hold for the call to `Bag.element` that this `for` loop makes.";
        ]);
  Harness.test "a precondition of a quantifier's call names the quantifier" (fun () ->
      expect_messages_saying Fixtures.Prover.all_small_in_a_short_bag
        [
          impl_precondition;
          "may not hold for the call to `Bag.element` that this quantifier makes.";
        ]);
  Harness.test "a panic condition of an operator's call names the operator" (fun () ->
      expect_message_saying Fixtures.Prover.sum_of_capped_money
        "may not hold for the call to `Money.add` that `left + right` makes, so the call may panic.")

let () =
  Harness.test "a pure call's result is in its type's range for every bound value" (fun () ->
      expect_proven Fixtures.Prover.each_element_at_most_the_maximum)

let () =
  Harness.test "a lambda in a quantifier that captures a bound value is known for each one"
    (fun () -> expect_proven Fixtures.Prover.quantified_lambda_capturing_a_bound_value);
  Harness.test "a lambda in a quantifier that captures no bound value is known for every argument"
    (fun () -> expect_proven Fixtures.Prover.quantified_lambda_capturing_no_bound_value)

let () =
  Harness.test "an insertion into a map, of a new key or one it has, is amortized" (fun () ->
      expect_proven Fixtures.Prover.map_put)

let applying = Fixtures.Prover.apply_of_a_change

let () =
  Harness.test "a lambda with a functional lambda inside that captures nothing it made is known"
    (fun () -> expect_proven (applying ^ Fixtures.Prover.nested_identity_lambda));
  Harness.test "a lambda with a functional lambda inside that captures its argument is known"
    (fun () -> expect_proven (applying ^ Fixtures.Prover.nested_lambda_returning_its_argument));
  Harness.test "a functional lambda inside that captures the argument is not one function"
    (fun () ->
      expect_not_proven (applying ^ Fixtures.Prover.nested_lambda_wrongly_constant) "prover.ensures")

let () =
  Harness.test "a lambda in a lambda's body knows the enclosing lambda's argument it captures"
    (fun () -> expect_proven Fixtures.Prover.filter_in_a_lambda_capturing_its_argument);
  Harness.test
    "a lambda in the body of a lambda that may panic knows the enclosing lambda's argument it \
     captures" (fun () ->
      expect_proven Fixtures.Prover.filter_in_a_lambda_that_may_panic_capturing_its_argument)

let () =
  Harness.test "a contract with branches, called under a quantifier on no bound value, holds there"
    (fun () -> expect_proven Fixtures.Prover.used_bits_under_a_quantifier);
  Harness.test "a derived ordering of a one-field record is its field's, for every value" (fun () ->
      expect_proven Fixtures.Prover.day_ordering_theorem);
  Harness.test "a derived ordering compares fields in order, for every value" (fun () ->
      expect_proven Fixtures.Prover.pair_ordering_theorem)

let () =
  Harness.test "a string's characters collect into a list in time linear in its length" (fun () ->
      expect_proven Fixtures.Prover.characters_collected_in_linear_time);
  Harness.test "a copy of a string or a list costs time in its length and one allocation" (fun () ->
      expect_proven Fixtures.Prover.copies_of_a_string_and_a_list_within_their_lengths);
  Harness.test "a copy of a string does not cost constant time" (fun () ->
      expect_not_proven Fixtures.Prover.copy_of_a_string_in_constant_time "prover.cost");
  Harness.test "a list of views passed `own` or `mut` holds no potential for its elements"
    (fun () -> expect_proven Fixtures.Prover.list_of_views_passed_on_in_constant_amortized_time);
  Harness.test "a loop that pushes views is charged no potential for their owners" (fun () ->
      expect_proven Fixtures.Prover.loops_pushing_views_within_an_amortized_bound);
  Harness.test "a copy of a list of views costs time in its length, whatever the strings' lengths"
    (fun () -> expect_proven Fixtures.Prover.copy_of_a_list_of_views_within_its_length);
  Harness.test "a copy of a list of views does not cost constant time" (fun () ->
      expect_not_proven Fixtures.Prover.copy_of_a_list_of_views_in_constant_time "prover.cost");
  Harness.test "a view holds no potential, so returning one costs constant amortized time"
    (fun () -> expect_proven Fixtures.Prover.view_returned_in_constant_amortized_time);
  Harness.test "a finite cursor collects through a bound in its remaining count of nexts" (fun () ->
      expect_proven Fixtures.Prover.finite_cursor_collected_generically);
  Harness.test "an amortized call of a supertrait's method through a subtrait bound is counted"
    (fun () -> expect_proven Fixtures.Prover.amortized_supertrait_method_under_a_subtrait_bound)

let () =
  Harness.test "sorting is n log n where the element's ordering is constant time" (fun () ->
      expect_proven Fixtures.Prover.sorts_in_n_log_n);
  Harness.test "sorting records with a derived ordering of a string field is not n log n" (fun () ->
      expect_not_proven Fixtures.Prover.sort_of_derived_people_in_n_log_n "prover.cost");
  Harness.test "a derived ordering of a recursive type has no constant time bound" (fun () ->
      expect_not_proven Fixtures.Prover.derived_ordering_of_a_chain_in_constant_time "prover.cost");
  Harness.test "a derived equality spends the equality of a list field" (fun () ->
      expect_not_proven Fixtures.Prover.derived_equality_of_tags_in_constant_time "prover.cost");
  Harness.test "derived methods of constant-time fields are constant time and allocate nothing"
    (fun () -> expect_proven Fixtures.Prover.derived_methods_of_constant_time_fields);
  Harness.test "a derived default spends its fields' defaults" (fun () ->
      expect_proven Fixtures.Prover.derived_default_of_settings);
  Harness.test "a derived default spends the allocation of a written list default" (fun () ->
      expect_not_proven Fixtures.Prover.derived_default_of_settings_without_allocations
        "prover.cost")

let () =
  Harness.test "a proof for a generic impl names its own generic parameters" (fun () ->
      expect_proven Fixtures.Prover.triangle_in_a_generic_impl);
  Harness.test "a law's proof names the law's parameters, where its requires hold" (fun () ->
      expect_proven Fixtures.Prover.sized_law_proof_naming_its_parameters);
  Harness.test "a law's proof reads the specifications that its own body holds" (fun () ->
      expect_proven Fixtures.Prover.masked_law_proof_reading_its_specifications)

let () =
  Harness.test "a failing bit-vector assertion in a law's proof is cited by its impl's diagnostic"
    (fun () ->
      let text = Fixtures.Prover.masked_law_with_a_bit_vector_assertion in
      let packages = Support.setup [ ("app.main", text) ] in
      match check packages (Support.parse_file "app.main") with
      | [ ({ notes = [ (cited, _) ]; _ } : Diagnostic.t) ] ->
          let quoted = String.sub text cited.start (cited.stop - cited.start) in
          if not (String.includes ~affix:"(bits & 15) < 8" quoted) then
            Harness.fail "cites %S" quoted
      | actual -> Harness.fail "%s" (String.concat ", " (Support.list_codes actual)))

let make_early_return_source ensures =
  "fn f(first: mut Int64, second: mut Int64) -> Int64\n  requires second < 100\n" ^ ensures
  ^ "  uses Tasks\n{\n  concurrent {\n    return 0\n    second += 1\n  }\n}\n"

let () =
  Harness.test "an early exit from a concurrent block does not know whether a later branch ran"
    (fun () ->
      expect_not_proven
        (make_early_return_source "  ensures second == old(second) + 1\n")
        "prover.ensures");
  Harness.test "an early exit from a concurrent block does not know that a later branch did not run"
    (fun () ->
      expect_not_proven
        (make_early_return_source "  ensures second == old(second)\n")
        "prover.ensures");
  Harness.test "an early exit from a concurrent block does not know whether an earlier branch ran"
    (fun () ->
      expect_not_proven Fixtures.Prover.concurrent_exit_after_an_earlier_branch "prover.ensures");
  Harness.test "an early exit from a concurrent for keeps the length of the collection it mutates"
    (fun () -> expect_proven Fixtures.Prover.concurrent_for_exit_keeping_the_length);
  Harness.test "a concurrent block with no early exit is read as its branches in order" (fun () ->
      expect_proven Fixtures.Prover.concurrent_block_bumping_two_counts)

let () =
  Harness.test "a file's proof states list proven and unproven obligations" (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Prover.element_sum_with_one_unchecked_index) ]
      in
      let states =
        Support.list_proof_states (Support.make_database packages) (Support.parse_file "app.main")
      in
      let failed = List.filter (fun (state : Database.proof_state) -> not state.is_proven) states in
      if List.length failed <> 1 || List.length states < 2 then
        Harness.fail "%d states, %d failed" (List.length states) (List.length failed));
  Harness.test "a call's requires that may not hold has a note at the clause" (fun () ->
      let text = Fixtures.Prover.halved_of_an_unchecked_count in
      let packages = Support.setup [ ("app.main", text) ] in
      match check packages (Support.parse_file "app.main") with
      | [ { notes = [ (span, _) ]; _ } ] ->
          let noted = String.sub text span.start (span.stop - span.start) in
          if noted <> "count > 0" then Harness.fail "the note is at `%s`" noted
      | actual -> Harness.fail "%s" (String.concat "; " (Support.list_codes actual)));
  Harness.test "the same failure on another path is reported once" (fun () ->
      let actual = list_codes Fixtures.Prover.index_without_a_bound_on_two_paths in
      if actual <> [ "prover.out_of_bounds" ] then Harness.fail "%s" (String.concat ", " actual))

let () =
  Harness.test "a function parameter of constant time is passed as one that terminates" (fun () ->
      expect_proven Fixtures.Prover.run_of_a_constant_time_task);
  Harness.test "a type's invariant must be well defined" (fun () ->
      expect_not_proven "type Ratio(top: Int64, bottom: Int64)\n  invariant top / bottom > 0\n"
        "prover.division");
  Harness.test "a type's invariant is well defined given the ones before it" (fun () ->
      expect_proven Fixtures.Prover.ratio_invariants);
  Harness.test "a requires is well defined given the requires before it, not those after" (fun () ->
      expect_proven Fixtures.Prover.requires_dividing_after_its_guard;
      expect_not_proven Fixtures.Prover.requires_dividing_before_its_guard "prover.division"
        ~fixed:
          ( "  requires 100 / divisor > 1\n  requires divisor != 0",
            "  requires divisor != 0\n  requires 100 / divisor > 1\n  requires divisor != 0" ));
  Harness.test "the right operand of `&&`, `||`, and `==>` in a requires relies on the left"
    (fun () ->
      expect_proven Fixtures.Prover.requires_reading_left_to_right;
      expect_not_proven Fixtures.Prover.requires_reading_an_element_before_its_bound
        "prover.out_of_bounds");
  Harness.test "an ensures must be well defined where the function returns" (fun () ->
      expect_not_proven Fixtures.Prover.ensures_dividing_by_a_parameter "prover.division"
        ~fixed:
          ( "  ensures result == 100 / divisor\n{",
            "  ensures result == 100 / divisor\n  requires divisor != 0\n{" ));
  Harness.test "a cost clause's bound must be well defined" (fun () ->
      let actual = list_codes Fixtures.Prover.cost_bound_reading_an_element in
      if not (List.mem "prover.out_of_bounds" actual) then
        Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a derived ordering of a record compares its fields in order" (fun () ->
      expect_proven Fixtures.Prover.version_less_by_major);
  Harness.test
    "a derived ordering compares fields in declaration order, not in the order of their names"
    (fun () -> expect_proven Fixtures.Prover.entry_ordering);
  Harness.test "a derived ordering of a record falls to the next field on a tie" (fun () ->
      expect_proven Fixtures.Prover.version_greater_by_minor);
  Harness.test "a derived ordering of a sum orders by variant first" (fun () ->
      expect_proven Fixtures.Prover.light_ordering);
  Harness.test "a derived ordering is not the reverse of itself" (fun () ->
      expect_not_proven Fixtures.Prover.version_greater_by_major "prover.ensures");
  Harness.test "recursion on an element of a field's list ends" (fun () ->
      expect_proven Fixtures.Prover.tree_visit_of_its_children);
  Harness.test "recursion on a value that is not a part does not end" (fun () ->
      expect_not_proven Fixtures.Prover.tree_visit_of_a_new_tree "prover.termination");
  Harness.test "a trait's provided body keeps the trait's clauses on its own" (fun () ->
      expect_not_proven Fixtures.Prover.sized_provided_last_index "prover.ensures");
  Harness.test "a trait's provided body that keeps its clauses proves" (fun () ->
      expect_proven Fixtures.Prover.sized_provided_halved);
  Harness.test "a call of a bound's method spends the time of that method" (fun () ->
      expect_proven Fixtures.Prover.contains_through_equal);
  Harness.test "the time of a bound's method is not free" (fun () ->
      let actual = list_codes Fixtures.Prover.contains_without_the_time_of_equal in
      if not (List.mem "prover.cost" actual) then
        Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "log of a number is its bit length" (fun () ->
      expect_proven Fixtures.Prover.integer_square_root);
  Harness.test "log of a bounded integer is at most its width" (fun () ->
      expect_proven Fixtures.Prover.digits_of_a_bounded_value);
  Harness.test "power of two numbers is their power" (fun () ->
      expect_proven Fixtures.Prover.table_of_time_power_of_two);
  Harness.test "a range mutated through a call mutates its run of the list" (fun () ->
      expect_proven ("" ^ Fixtures.Prover.zeroed_range_of_a_list));
  Harness.test "a range mutated through a call mutates nothing more than it says" (fun () ->
      expect_not_proven ("" ^ Fixtures.Prover.zeroed_range_ensured_past_its_run) "prover.ensures");
  Harness.test "an unsigned left shift that fits multiplies by a power of two" (fun () ->
      expect_proven Fixtures.Prover.shift_by_four_of_a_small_byte);
  Harness.test "an unsigned right shift divides by a power of two" (fun () ->
      expect_proven Fixtures.Prover.right_shift_by_two);
  Harness.test "a left shift that may not fit is not known to multiply" (fun () ->
      expect_not_proven Fixtures.Prover.shift_by_four_of_any_byte "prover.ensures");
  Harness.test "a loop that mutates a range of any elements under a cost clause" (fun () ->
      expect_proven Fixtures.Prover.swap_each);
  Harness.test "a quantifier's body must be well defined" (fun () ->
      expect_not_proven Fixtures.Prover.requires_quantifier_reading_past_the_end
        "prover.out_of_bounds");
  Harness.test "a quantifier's body within its range is well defined" (fun () ->
      expect_proven Fixtures.Prover.requires_quantifier_within_the_list);
  Harness.test "a call under a quantifier gives a value for each value, not one for all" (fun () ->
      expect_not_proven Fixtures.Prover.same_under_a_quantifier "prover.ensures");
  Harness.test "alternatives bind each name to the part that matched" (fun () ->
      expect_proven Fixtures.Prover.or_pattern_binding_a_side_value);
  Harness.test "a match mut binding of alternatives is the part of the alternative that matched"
    (fun () -> expect_proven Fixtures.Prover.match_mut_on_sides);
  Harness.test "a match mut binding of alternatives is no other alternative's part" (fun () ->
      expect_not_proven Fixtures.Prover.match_mut_on_sides_with_a_wrong_ensures "prover.ensures");
  Harness.test "a `mut` element argument in a condition is written back on each path" (fun () ->
      expect_proven Fixtures.Prover.if_condition_bumping_an_element);
  Harness.test "a `mut` element argument in a condition is written back where the condition holds"
    (fun () ->
      expect_not_proven Fixtures.Prover.if_condition_bumping_a_positive_element "prover.ensures");
  Harness.test "a `mut` element argument in a condition is written back where the condition fails"
    (fun () ->
      expect_not_proven Fixtures.Prover.if_condition_bumping_a_negative_element "prover.ensures");
  Harness.test "a `mut` element argument in a loop's condition is written back" (fun () ->
      expect_proven Fixtures.Prover.while_condition_bumping_an_element);
  Harness.test
    "a `while` compares its measure before each evaluation of its condition, so a condition that \
     undoes the body does not prove termination" (fun () ->
      expect_not_proven Fixtures.Prover.loop_condition_undoing_the_body "prover.termination");
  Harness.test
    "a `mut` element argument in the right operand of && is written back where the operand ran"
    (fun () -> expect_proven Fixtures.Prover.and_operand_bumping_an_element_under_a_flag);
  Harness.test "a `mut` element argument in the right operand of && changes the element" (fun () ->
      expect_not_proven Fixtures.Prover.and_operand_bumping_a_negative_element "prover.ensures")

let () =
  let make_self_comparison operator =
    let symbol = Logic.Symbol.Variable { label = "compared"; numbers = [] } in
    {
      Logic.declarations = [ Logic.Constant (symbol, Logic.Int) ];
      facts = [];
      goal = Logic.Operation (operator, [ Logic.Symbol symbol; Logic.Symbol symbol ]);
    }
  in
  Harness.test "a value passed as it was received asks the solver nothing about its invariant"
    (fun () ->
      let database =
        Support.make_database
          (Support.setup [ ("app.main", Fixtures.Prover.value_with_an_invariant_passed_unchanged) ])
      in
      match
        List.filter
          (fun (state : Database.proof_state) -> state.site.code = "prover.invariant")
          (Support.list_proof_states database (Support.parse_file "app.main"))
      with
      | [] -> ()
      | states -> Harness.fail "%d obligations about the invariant" (List.length states));
  Harness.test "a sum, a difference and a product of constants are constants" (fun () ->
      let unknown = Logic.Symbol (Logic.Symbol.Variable { label = "unknown"; numbers = [] }) in
      if
        Logic.add (Logic.int 0) unknown <> unknown
        || Logic.subtract unknown unknown <> Logic.int 0
        || Logic.multiply unknown (Logic.int 1) <> unknown
        || Logic.add (Logic.int 2) (Logic.multiply (Logic.int 3) (Logic.int 4)) <> Logic.int 14
      then Harness.fail "a constructor kept an operation on a constant");
  Harness.test "a comparison is decided where its sides differ by a constant inside an application"
    (fun () ->
      let unknown = Logic.Symbol (Logic.Symbol.Variable { label = "unknown"; numbers = [] }) in
      let apply argument =
        Logic.Apply (Logic.Symbol.Variable { label = "function"; numbers = [] }, [ argument ])
      in
      let with_a_zero = apply (Logic.Operation (Add, [ unknown; Logic.int 0 ])) in
      if not (Logic.is_refuted (Logic.less with_a_zero (apply unknown))) then
        Harness.fail "a term below itself is not refuted";
      if not (Logic.is_valid (Logic.less_equal with_a_zero (apply unknown))) then
        Harness.fail "a term at most itself is not valid");
  Harness.test "two facts that differ only deep inside hash differently" (fun () ->
      let make_symbol label = Logic.Symbol (Logic.Symbol.Variable { label; numbers = [] }) in
      let nest last =
        List.fold_right
          (fun index inner -> Logic.Operation (And, [ make_symbol (string_of_int index); inner ]))
          (List.init 300 Fun.id) (make_symbol last)
      in
      if Logic.hash_term (nest "first") = Logic.hash_term (nest "second") then
        Harness.fail "the hash reads only the start of a term");
  Harness.test "a conjunction under a premise splits into one pruned query per conjunct" (fun () ->
      let make_symbol label = Logic.Symbol.Variable { label; numbers = [] } in
      let premise = make_symbol "premise"
      and first = make_symbol "first"
      and second = make_symbol "second" in
      let query =
        {
          Logic.declarations =
            List.map (fun symbol -> Logic.Constant (symbol, Logic.Bool)) [ premise; first; second ];
          facts = [ Logic.Symbol first ];
          goal =
            Logic.( ==> ) (Logic.Symbol premise)
              (Logic.( &&& ) (Logic.Symbol first) (Logic.Symbol second));
        }
      in
      match Logic.list_conjunct_queries query with
      | [ about_first; about_second ] ->
          if about_first.goal <> Logic.( ==> ) (Logic.Symbol premise) (Logic.Symbol first) then
            Harness.fail "the first query's goal is not the first conjunct";
          if about_second.goal <> Logic.( ==> ) (Logic.Symbol premise) (Logic.Symbol second) then
            Harness.fail "the second query's goal is not the second conjunct";
          if about_first.facts <> [ Logic.Symbol first ] then
            Harness.fail "the first query lost the fact it reads";
          if about_second.facts <> [] then
            Harness.fail "the second query keeps a fact that its goal does not reach"
      | queries -> Harness.fail "%d queries" (List.length queries));
  let started = ref [] in
  let find_solver () =
    match Solver.find () with
    | Ok solver ->
        started := solver :: !started;
        solver
    | Error message -> Harness.fail "%s" message
  in
  let test name body =
    Harness.test name (fun () ->
        Fun.protect body ~finally:(fun () ->
            List.iter Solver.stop !started;
            started := []))
  in
  let solve_one ?find_output solver request =
    List.hd (Solver.solve_all ?find_output solver [ request ])
  in
  let find_stored_output (solved : Solver.solved) input =
    List.find_map
      (fun (run : Solver.run) -> if run.input = input then Some run.output else None)
      solved.runs
  in
  test "a stored run is read by its input, and Z3 is not run" (fun () ->
      let request = Solver.make_request (make_self_comparison Logic.Greater_equal) in
      let solver = find_solver () in
      let find_output input = if input = Solver.show_input request then Some "unsat\n" else None in
      if (solve_one ~find_output solver request).answer <> Solver.Proven then
        Harness.fail "expected the stored answer";
      if Solver.For_testing.count_queries_run solver <> 0 then Harness.fail "ran Z3");
  test "each run that answers a request is reported with its input and Z3's output" (fun () ->
      let request = Solver.make_request (make_self_comparison Logic.Less_equal) in
      let solver = find_solver () in
      match (solve_one solver request).runs with
      | [ { input; output } ] ->
          if input <> Solver.show_input request then Harness.fail "reported the input %S" input;
          if not (String.starts_with ~prefix:"unsat" output) then
            Harness.fail "reported the output %S" output
      | runs -> Harness.fail "reported %d runs" (List.length runs));
  test "requests with the same input are answered by one run" (fun () ->
      let request = Solver.make_request (make_self_comparison Logic.Less) in
      let solver = find_solver () in
      ignore (Solver.solve_all solver [ request; request ]);
      if Solver.For_testing.count_queries_run solver <> 1 then
        Harness.fail "ran %d queries" (Solver.For_testing.count_queries_run solver));
  test "one Z3 process answers every query that a solver runs in turn" (fun () ->
      let directory = Harness.make_scratch_directory "z3" in
      let launches = Filename.concat directory "launches" in
      Harness.write_files directory
        [ ("z3", Printf.sprintf "#!/bin/sh\necho launched >> %s\nexec z3 \"$@\"\n" launches) ];
      Unix.chmod (Filename.concat directory "z3") 0o755;
      Unix.putenv "TRUSS_Z3" (Filename.concat directory "z3");
      let solver = find_solver () in
      List.iter
        (fun operator ->
          ignore (solve_one solver (Solver.make_request (make_self_comparison operator))))
        [ Logic.Less; Logic.Less_equal; Logic.Greater ];
      match String.split_on_char '\n' (String.trim (File_system.read launches)) with
      | [ _ ] -> ()
      | launched -> Harness.fail "launched Z3 %d times" (List.length launched));
  test "a Z3 that names its build after its version has the version before the build" (fun () ->
      let directory = Harness.make_scratch_directory "z3" in
      Harness.write_files directory
        [
          ( "z3",
            String.concat "\n"
              [
                "#!/bin/sh";
                "while read -r line; do";
                "  case \"$line\" in";
                "    '(get-info :version)') echo '(:version \"5.3.3 - build hashcode 0\")' ;;";
                "    '(echo \"truss.end-of-answer\")') echo truss.end-of-answer ;;";
                "  esac";
                "done";
                "";
              ] );
        ];
      Unix.chmod (Filename.concat directory "z3") 0o755;
      Unix.putenv "TRUSS_Z3" (Filename.concat directory "z3");
      ignore (find_solver ()));
  test "a query's declarations are forgotten before the next query" (fun () ->
      let flag = Logic.Symbol.Variable { label = "flag"; numbers = [] } in
      let excluded_middle =
        {
          Logic.declarations = [ Logic.Constant (flag, Logic.Bool) ];
          facts = [];
          goal = Logic.Operation (Or, [ Logic.Symbol flag; Logic.not_ (Logic.Symbol flag) ]);
        }
      in
      let solver = find_solver () in
      let answers =
        List.map
          (fun query -> (solve_one solver (Solver.make_request query)).answer)
          [ make_self_comparison Logic.Less_equal; excluded_middle ]
      in
      if answers <> [ Solver.Proven; Solver.Proven ] then
        Harness.fail "a constant of another sort under the same name was not proven");
  let find_obligation_query text code =
    let packages = Support.setup [ ("app.main", text) ] in
    let key = List.hd (Support.list_declarations packages (Support.parse_module "app.main")) in
    match
      Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main") key.key
    with
    | Obligations { obligations; _ } ->
        List.find_map
          (fun (obligation : Prover.Obligation.t) ->
            if Catalog.Prover_description.find_code obligation.obligation = code then
              Some obligation.query
            else None)
          obligations
    | Unsupported _ | Not_proven_here -> None
  in
  test "an unknown answer without an uninterpreted sort is not searched further" (fun () ->
      match (find_obligation_query Fixtures.Prover.sum_of_two_cubes Ensures, find_solver ()) with
      | None, _ -> Harness.fail "no obligation of the `ensures`"
      | Some query, solver ->
          if (solve_one solver (Solver.make_request query)).answer <> Unknown Out_of_steps then
            Harness.fail "expected an unknown answer from the step limit";
          if Solver.For_testing.count_queries_run solver <> 1 then
            Harness.fail "ran %d queries" (Solver.For_testing.count_queries_run solver));
  let power_of_itself_is_three =
    let symbol = Logic.Symbol.Variable { label = "base"; numbers = [] } in
    {
      Logic.declarations = [ Logic.Constant (symbol, Logic.Int) ];
      facts = [];
      goal =
        Logic.not_
          (Logic.equal
             (Logic.Operation (Power, [ Logic.Symbol symbol; Logic.Symbol symbol ]))
             (Logic.int 3));
    }
  in
  test "an unknown answer before the step limit carries Z3's reason" (fun () ->
      let query = power_of_itself_is_three in
      match (solve_one (find_solver ()) (Solver.make_request query)).answer with
      | Unknown (Incomplete reason) ->
          if not (String.includes ~affix:"incomplete (theory arithmetic)" reason) then
            Harness.fail "reason %S" reason
      | _ -> Harness.fail "expected an unknown answer with Z3's reason");
  let expect_answered_from_runs request =
    let first = find_solver () and second = find_solver () in
    let solved = solve_one first request in
    if (solve_one ~find_output:(find_stored_output solved) second request).answer <> solved.answer
    then Harness.fail "the stored runs gave another answer";
    if Solver.For_testing.count_queries_run second <> 0 then Harness.fail "ran Z3 again";
    solved.answer
  in
  test "an unknown answer's reason is read back from its stored runs" (fun () ->
      match expect_answered_from_runs (Solver.make_request power_of_itself_is_three) with
      | Unknown (Incomplete _) -> ()
      | _ -> Harness.fail "expected an unknown answer with Z3's reason");
  test "a falsifiable answer is read back from its stored runs" (fun () ->
      match expect_answered_from_runs (Solver.make_request (make_self_comparison Logic.Less)) with
      | Falsifiable -> ()
      | _ -> Harness.fail "expected a falsifiable answer");
  test "an obligation that the solver stops on before the step limit names Z3's reason" (fun () ->
      let solver =
        Solver.For_testing.make ~run_z3:(fun _ ->
            "unknown\n(:reason-unknown \"(incomplete quantifiers)\")\n(:rlimit 1)\n")
      in
      let database =
        Support.make_database
          (Support.setup [ ("app.main", Fixtures.Prover.addition_that_can_overflow) ])
      in
      let file = Support.parse_file "app.main" in
      Database.decide (Support.prove database file) (Lazy.from_val solver);
      match Database.list_proof_diagnostics database file with
      | [ diagnostic ] ->
          if
            not
              (String.includes ~affix:"Z3 gives the reason `(incomplete quantifiers)`"
                 diagnostic.message)
          then Harness.fail "message %S" diagnostic.message
      | diagnostics -> Harness.fail "%d diagnostics" (List.length diagnostics));
  test "deciding an edited body runs Z3 only for the queries that changed" (fun () ->
      let file = Support.parse_file "app.main" in
      let database =
        Support.make_database
          (Support.setup [ ("app.main", Fixtures.Prover.two_bounded_additions) ])
      in
      let decide () =
        let solver = find_solver () in
        Database.decide (Support.prove database file) (Lazy.from_val solver);
        Solver.For_testing.count_queries_run solver
      in
      let from_nothing = decide () in
      Database.update database
        [ (file, Some Fixtures.Prover.two_bounded_additions_with_the_second_changed) ];
      let after_the_edit = decide () in
      if after_the_edit <> 1 then
        Harness.fail "ran %d queries after the edit, and %d from nothing" after_the_edit
          from_nothing);
  test "a function defined by a quantified formula reaches the solver as a definition" (fun () ->
      match find_obligation_query Fixtures.Prover.increment_of_a_word_count Overflow with
      | None -> Harness.fail "no obligation of the addition"
      | Some query ->
          let text = Logic.show_query query in
          if not (String.includes ~affix:"(define-fun " text) then Harness.fail "query %s" text);
  test "a query's text names nothing by its Truss name" (fun () ->
      let packages = Support.setup [ ("app.main", Fixtures.Prover.addition_that_can_overflow) ] in
      let key = List.hd (Support.list_declarations packages (Support.parse_module "app.main")) in
      match
        Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main") key.key
      with
      | Obligations { obligations = [ obligation ]; _ } ->
          let text = Logic.show_query obligation.query in
          if String.includes ~affix:"count" text then Harness.fail "the text names `count`: %s" text
      | _ -> Harness.fail "expected one obligation");
  test "renaming a function and its parameter gives the same query" (fun () ->
      let key_of text =
        let packages = Support.setup [ ("app.main", text) ] in
        let key = List.hd (Support.list_declarations packages (Support.parse_module "app.main")) in
        match
          Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main")
            key.key
        with
        | Obligations { obligations = [ obligation ]; _ } -> Logic.show_query obligation.query
        | _ -> "none"
      in
      let first = key_of Fixtures.Prover.addition_that_can_overflow in
      let second = key_of Fixtures.Prover.addition_of_a_total_that_can_overflow in
      if first <> second || first = "none" then Harness.fail "%s and %s" first second)

let () =
  Harness.test "a range of a whole array is within it" (fun () ->
      expect_proven Fixtures.Prover.reverse_of_a_whole_array);
  Harness.test "a loop that mutates an array's elements keeps their potentials" (fun () ->
      expect_proven Fixtures.Prover.array_reset);
  Harness.test "a range of an array is within it only as far as its count" (fun () ->
      expect_not_proven Fixtures.Prover.reverse_of_an_array_after_its_first "prover.out_of_bounds");
  Harness.test "a quantifier ranges between an Integer and a UInt64 in either order" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_ranges_between_integer_types)

let () =
  Harness.test "a nested call's arguments are written once, however deep it nests" (fun () ->
      let make_most depth =
        let nested =
          List.fold_left
            (fun inner _ -> "spread(" ^ inner ^ ")")
            "value + 12345 - 12345" (List.init depth Fun.id)
        in
        let packages =
          Support.setup
            [
              ( "app.main",
                "fn spread(value: Int64) -> Int64\n\
                \  requires 0 <= value && value < 1000\n\
                \  ensures result == value\n\
                \  cost time O(1)\n\
                 {\n\
                \  (value + value + value + value) / 4\n\
                 }\n\n\
                 fn f(value: Int64) -> Int64\n\
                \  requires 0 <= value && value < 100\n\
                \  ensures result == value\n\
                \  cost time O(1)\n\
                 {\n\
                \  " ^ nested ^ "\n}\n" );
            ]
        in
        let key =
          List.find
            (fun (declaration : Resolve.Names.declaration) ->
              Path.equal declaration.key.path (Support.make_top_path "app.main" "f"))
            (Support.list_declarations packages (Support.parse_module "app.main"))
        in
        match
          Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main")
            key.key
        with
        | Obligations { obligations; _ } ->
            List.fold_left
              (fun most (obligation : Prover.Obligation.t) ->
                let text = Logic.show_query obligation.query in
                max most (String.find_all ~sub:"12345" (fun _ matches -> matches + 1) text 0))
              0 obligations
        | _ -> Harness.fail "expected obligations"
      in
      let shallow = make_most 3 and deep = make_most 6 in
      if deep > shallow then
        Harness.fail "written %d times nested 3 deep, %d times 6 deep" shallow deep);
  Harness.test "a callee is known by its contract, not its body" (fun () ->
      expect_not_proven Fixtures.Prover.halved_known_by_its_contract "prover.ensures");
  Harness.test "an impl's method is known by its contract, not its body" (fun () ->
      expect_not_proven Fixtures.Prover.measured_size_known_by_its_contract "prover.ensures");
  Harness.test "a provided method is known by its contract, not its body" (fun () ->
      expect_not_proven Fixtures.Prover.counted_provided_method_known_by_its_contract
        "prover.ensures");
  Harness.test "a provided method's ensures is known through a bound" (fun () ->
      expect_proven Fixtures.Prover.counted_provided_method_through_a_bound);
  Harness.test "a contract that states the body gives what the body would" (fun () ->
      expect_proven Fixtures.Prover.halved_ensuring_its_body)

let variable label = Logic.Symbol.Variable { label; numbers = [] }

let render_triggered fact =
  let open Logic in
  Logic.show_query
    {
      declarations =
        [
          Function (variable "f", [ Int ], Int);
          Function (variable "g", [ Int ], Int);
          Function (variable "h", [ Int; Int ], Int);
          Constant (variable "n", Int);
        ];
      facts = [ fact ];
      goal = greater (Apply (variable "f", [ Symbol (variable "n") ])) (int 0);
    }

let () =
  let open Logic in
  let i_term = Symbol (variable "i") and j_term = Symbol (variable "j") in
  let applied_f term = Apply (variable "f", [ term ])
  and applied_g term = Apply (variable "g", [ term ]) in
  let positive term = greater term (int 0) in
  let expect fact fragment =
    let text = render_triggered fact in
    if not (String.includes ~affix:fragment text) then
      Harness.fail "expected %s in %s" fragment text
  in
  Harness.test "a quantified fact triggers on an application of its variable" (fun () ->
      expect
        (forall
           ([ (variable "i", Int) ], greater_equal i_term (int 0) ==> positive (applied_f i_term)))
        ":pattern ((x0 b0))");
  Harness.test "a trigger has no arithmetic on a bound variable" (fun () ->
      let text =
        render_triggered
          (forall ([ (variable "i", Int) ], positive (applied_f (add i_term (int 1)))))
      in
      if String.includes ~affix:":pattern" text then Harness.fail "%s" text);
  Harness.test "a trigger that would match its own body's larger term is passed over" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int) ],
             less (applied_f i_term) (applied_f (add i_term (int 1)))
             &&& positive (applied_g i_term) ))
        ":pattern ((x2 b0)))");
  Harness.test "a definition triggers on the term it defines" (fun () ->
      let text =
        render_triggered
          (forall
             ([ (variable "i", Int) ], equal (applied_f i_term) (add (applied_g i_term) (int 1))))
      in
      if
        (not (String.includes ~affix:":pattern ((x0 b0)))" text))
        || String.includes ~affix:":pattern ((x1" text
      then Harness.fail "%s" text);
  let make_query fact =
    {
      declarations =
        [
          Function (variable "f", [ Int ], Int);
          Function (variable "g", [ Int ], Int);
          Constant (variable "n", Int);
        ];
      facts = [ fact ];
      goal = greater (Apply (variable "f", [ Symbol (variable "n") ])) (int 0);
    }
  in
  Harness.test "a quantified fact with no trigger is told apart" (fun () ->
      if
        not
          (has_untriggered_fact
             (make_query
                (forall ([ (variable "i", Int) ], positive (applied_f (add i_term (int 1)))))))
      then Harness.fail "a fact on f(i + 1) alone has no trigger";
      if
        has_untriggered_fact
          (make_query (forall ([ (variable "i", Int) ], positive (applied_f i_term))))
      then Harness.fail "a fact on f(i) has one";
      if
        has_untriggered_fact
          ~is_counted:(fun _ -> false)
          (make_query (forall ([ (variable "i", Int) ], positive (applied_f (add i_term (int 1))))))
      then Harness.fail "a fact that is not counted is told apart");
  Harness.test "variables named by no one application share a trigger" (fun () ->
      expect
        (forall
           ([ (variable "i", Int); (variable "j", Int) ], less (applied_f i_term) (applied_g j_term)))
        ":pattern ((x0 b0) (x2 b1))");
  let count_patterns text = String.find_all ~sub:":pattern" (fun _ matches -> matches + 1) text 0 in
  Harness.test
    "transitivity triggers on all three of its applications, so it makes no matching loop"
    (fun () ->
      let k_term = Symbol (variable "k") in
      let at_most first second = less_equal (Apply (variable "h", [ first; second ])) (int 0) in
      let text =
        render_triggered
          (forall
             ( [ (variable "i", Int); (variable "j", Int); (variable "k", Int) ],
               at_most i_term j_term &&& at_most j_term k_term ==> at_most i_term k_term ))
      in
      if
        count_patterns text <> 1
        || not (String.includes ~affix:":pattern ((x2 b0 b1) (x2 b0 b2) (x2 b1 b2))" text)
      then Harness.fail "%s" text);
  Harness.test "an equation between two applications triggers on either" (fun () ->
      let text =
        render_triggered
          (forall ([ (variable "i", Int) ], equal (applied_f i_term) (applied_g i_term)))
      in
      if count_patterns text <> 2 then Harness.fail "%s" text)

let bump = Fixtures.Prover.bump

let () =
  Harness.test "a mutation on the right of && happens only where the left holds" (fun () ->
      expect_proven (bump ^ Fixtures.Prover.mutation_on_the_right_of_and));
  Harness.test "a mutation on the right of || is not known to have happened" (fun () ->
      expect_not_proven (bump ^ Fixtures.Prover.mutation_on_the_right_of_or) "prover.ensures")

let apply_function = Fixtures.Prover.apply_function

let () =
  Harness.test "a pure function value gives the same result for the same argument" (fun () ->
      expect_proven Fixtures.Prover.terminating_measure_compared_with_itself);
  Harness.test "a function value that uses a capability may give different results" (fun () ->
      expect_not_proven Fixtures.Prover.clock_reading_compared_with_itself "prover.ensures");
  Harness.test "a function value that may run forever is a fresh result" (fun () ->
      expect_not_proven Fixtures.Prover.measure_that_may_run_forever_compared_with_itself
        "prover.ensures");
  Harness.test "a lambda applied is its body" (fun () ->
      expect_proven (apply_function ^ Fixtures.Prover.apply_of_a_halving_lambda));
  Harness.test "a lambda whose body is not its definition gives its body's facts" (fun () ->
      expect_proven (apply_function ^ Fixtures.Prover.apply_of_an_incrementing_lambda_ensured_four));
  Harness.test "a lambda body's facts are about its own argument" (fun () ->
      expect_not_proven
        (apply_function ^ Fixtures.Prover.apply_of_an_incrementing_lambda_ensured_three)
        "prover.ensures");
  let halved = Fixtures.Prover.halved in
  Harness.test "a named function with a requires, as a value, keeps its ensures" (fun () ->
      expect_proven (halved ^ Fixtures.Prover.halved_as_a_value_ensured_at_most));
  Harness.test "a named function, as a value, gives no more than its ensures" (fun () ->
      expect_not_proven
        (halved ^ Fixtures.Prover.halved_as_a_value_ensured_smaller)
        "prover.ensures");
  Harness.test "a lambda applied knows its captures" (fun () ->
      expect_proven (apply_function ^ Fixtures.Prover.apply_of_a_lambda_capturing_a_floor));
  Harness.test "two lambdas with the same body are the same function" (fun () ->
      expect_proven Fixtures.Prover.tally_of_equal_lambdas);
  Harness.test "lambdas with different bodies are not known to be the same function" (fun () ->
      expect_not_proven Fixtures.Prover.tally_of_different_lambdas "prover.ensures");
  Harness.test "a named pure function applied is the function" (fun () ->
      expect_proven (Fixtures.Prover.half ^ apply_function ^ Fixtures.Prover.apply_of_half))

let () =
  Harness.test "a specification spends nothing, whatever it calls" (fun () ->
      expect_proven Fixtures.Prover.requires_calling_keep)

let () =
  Harness.test "appending adds the new element's measure to a sum" (fun () ->
      expect_proven Fixtures.Prover.sum_of_lengths_after_an_append);
  Harness.test "a sum is not known to be anything else" (fun () ->
      expect_not_proven Fixtures.Prover.sum_of_lengths_after_an_append_ensured_unchanged
        "prover.ensures");
  Harness.test "a loop whose iterations cost different amounts is bounded by a sum" (fun () ->
      expect_proven Fixtures.Prover.count_cells);
  Harness.test "a loop's bound that leaves out its iterations' sum does not hold" (fun () ->
      expect_not_proven Fixtures.Prover.count_cells_in_rows_time "prover.cost")

let () =
  Harness.test "a permutation of a range argument is a permutation of the whole range" (fun () ->
      expect_proven Fixtures.Prover.permutation_through_a_range_argument);
  Harness.test "a permutation keeps every bound of its elements" (fun () ->
      expect_proven Fixtures.Prover.bound_kept_through_a_permutation);
  Harness.test "a permutation does not strengthen a bound of its elements" (fun () ->
      expect_not_proven Fixtures.Prover.bound_strengthened_through_a_permutation "prover.ensures");
  Harness.test "sorting both parts around a pivot sorts the range" (fun () ->
      expect_proven Fixtures.Prover.sorted_parts_around_a_pivot);
  Harness.test "a range of a sequence holds its elements from the range's start" (fun () ->
      expect_proven Fixtures.Prover.range_of_a_sequence);
  Harness.test "a range of a sequence is proven within the sequence" (fun () ->
      expect_not_proven Fixtures.Prover.range_of_a_sequence_past_its_end "prover.out_of_bounds")

let check_in_standard text =
  check_file
    (Support.extend_standard_library (Support.setup [ ("standard.probe", text) ]))
    (Support.parse_file "standard.probe")

let expect_not_proven_in_standard = Support.expect_diagnostic ~list_diagnostics:check_in_standard

let expect_proven_in_standard text =
  match check_in_standard text with
  | [] -> ()
  | actual ->
      Harness.fail "%s"
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual))

let () =
  Harness.test "two calls of a function that uses `System` are not known to return one value"
    (fun () ->
      let probe = Support.parse_file "standard.probe" in
      let database =
        Support.extend_standard_library
          [
            {
              name = Path.standard_package;
              dependencies = [];
              files = [ (probe, Fixtures.Prover.error_number_read_twice) ];
            };
          ]
      in
      match Support.list_codes (check_file database probe) with
      | [ "prover.ensures" ] -> ()
      | codes -> Harness.fail "reported [%s]" (String.concat "; " codes))

let () =
  Harness.test "a view of a scalar ends within the address space and is not at zero" (fun () ->
      expect_proven_in_standard Fixtures.Prover.view_address_placed)

let () =
  Harness.test "zero has no ones" (fun () ->
      expect_proven_in_standard Fixtures.Prover.count_ones_of_zero);
  Harness.test "the ones of a value fit below its bit length" (fun () ->
      expect_proven_in_standard Fixtures.Prover.ones_below_the_bit_length);
  Harness.test "the lowest one is below the bit length" (fun () ->
      expect_proven_in_standard Fixtures.Prover.lowest_one_below_the_bit_length);
  Harness.test "every one below a power of two is counted" (fun () ->
      expect_proven_in_standard Fixtures.Prover.count_ones_below_a_power_of_two);
  Harness.test "a value may have ones" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.count_ones_ensured_zero "prover.ensures")

let () =
  Harness.test "an intrinsic operation has its operator's facts" (fun () ->
      expect_proven_in_standard Fixtures.Prover.intrinsic_mask);
  Harness.test "an intrinsic shift has its operator's obligation on the amount" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.intrinsic_shift_left "prover.shift"
        ~fixed:
          ( "fn shifted(value: UInt64, amount: UInt64) -> UInt64 {",
            "fn shifted(value: UInt64, amount: UInt64) -> UInt64\n  requires amount < 64\n{" )
        ~alternatives:
          [
            ( "fn shifted(value: UInt64, amount: UInt64) -> UInt64 {",
              "fn shifted(value: UInt64, amount: UInt64) -> UInt64\n  uses Panic\n{" );
          ]);
  Harness.test "a character made from an integer must be a Unicode scalar value" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.character_converted_from_a_code
        "prover.requires"
        ~fixed:
          ( "fn character(code: UInt32) -> Character {",
            "fn character(code: UInt32) -> Character\n\
            \  requires (0 <= code && code <= 55295) || (57344 <= code && code <= 1114111)\n\
             {" ))

let () =
  Harness.test "a float converted to a type parameter is unsupported, not unchecked" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.float_converted_to_a_type_parameter
        "prover.unsupported");
  Harness.test "an intrinsic sum at a type parameter with no integer bound is unsupported"
    (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.intrinsic_sum_at_a_type_parameter
        "prover.unsupported")

let () =
  Harness.test "an element of a storage is read only at an index within it" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.storage_read_at_an_unchecked_index
        "prover.requires");
  Harness.test "an element of a storage at an index below its length proves" (fun () ->
      expect_proven_in_standard Fixtures.Prover.storage_read_at_a_checked_index);
  Harness.test "a storage is popped only when it holds an element" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.storage_popped_without_a_length
        "prover.requires");
  Harness.test "a view is ranged only within its length" (fun () ->
      expect_not_proven_in_standard Fixtures.Prover.view_ranged_past_its_end "prover.requires")

let () =
  let apply = Fixtures.Prover.apply_bounded_by_the_time_of_change in
  Harness.test "a bound that names the time of a callback takes the time of the function passed"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_passing_the_time_of_quick_through));
  Harness.test "a function without a time clause passes a function without one" (fun () ->
      expect_proven (apply ^ Fixtures.Prover.apply_of_slow_without_a_time_clause));
  Harness.test
    "a call that uses nothing is in the logic, whatever its callee's capability parameter"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_in_an_ensures));
  Harness.test "a function that uses RunForever passes a lambda with a loop without a measure"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_of_a_lambda_looping_without_a_measure));
  Harness.test "an operator on a bound type terminates" (fun () ->
      expect_proven Fixtures.Prover.sum_of_a_bound_type_in_a_function_that_terminates)

let () =
  let callbacks = Fixtures.Prover.apply_and_each_bounded_by_the_allocations_of_a_callback in
  Harness.test "one call of a callback spends the callback's allocations" (fun () ->
      expect_proven callbacks);
  Harness.test "two calls of a callback are not within the allocations of one" (fun () ->
      expect_not_proven Fixtures.Prover.apply_twice_bounded_by_the_allocations_of_one_call
        "prover.cost");
  Harness.test "two calls of a callback spend its allocations twice" (fun () ->
      expect_proven Fixtures.Prover.apply_twice_bounded_by_the_allocations_of_two_calls);
  Harness.test "a loop of calls of a callback is not within the allocations of one call" (fun () ->
      expect_not_proven Fixtures.Prover.each_bounded_by_the_allocations_of_one_visit "prover.cost");
  Harness.test "an order bound names the allocations of a callback" (fun () ->
      expect_proven Fixtures.Prover.each_of_the_order_of_the_allocations_of_visit);
  Harness.test "a lambda that allocates nothing passes an allocation bound of zero" (fun () ->
      expect_proven (callbacks ^ Fixtures.Prover.apply_of_a_lambda_that_allocates_nothing));
  Harness.test "a lambda that allocates does not pass an allocation bound of zero" (fun () ->
      expect_not_proven (callbacks ^ Fixtures.Prover.apply_of_a_lambda_that_allocates) "prover.cost");
  Harness.test "a lambda that allocates once passes an allocation bound of one" (fun () ->
      expect_proven (callbacks ^ Fixtures.Prover.apply_of_a_lambda_that_allocates_once));
  Harness.test "a lambda that allocates does not pass a bound of zero allocated bytes" (fun () ->
      expect_not_proven
        (callbacks ^ Fixtures.Prover.apply_of_a_lambda_that_allocates_bytes)
        "prover.cost");
  Harness.test "a named function passed for a callback spends the allocations its clause states"
    (fun () ->
      expect_proven (callbacks ^ Fixtures.Prover.apply_of_a_named_function_with_an_allocation_bound));
  Harness.test "a named function without an allocation bound has unbounded allocations" (fun () ->
      expect_not_proven
        (callbacks ^ Fixtures.Prover.apply_of_a_named_function_without_an_allocation_bound)
        "prover.cost";
      expect_not_proven
        (callbacks ^ Fixtures.Prover.apply_of_a_named_function_without_a_bound_on_its_bytes)
        "prover.cost");
  Harness.test
    "a lambda that calls a function without an allocation bound has unbounded allocations"
    (fun () ->
      expect_not_proven
        (callbacks
       ^ Fixtures.Prover.apply_of_a_lambda_calling_a_function_without_an_allocation_bound)
        "prover.cost");
  Harness.test "a callback passed on spends its own allocations" (fun () ->
      expect_proven
        (callbacks ^ Fixtures.Prover.apply_forwarding_a_callback_bounded_by_its_allocations))

let () =
  Harness.test "the allocations of a callback are within the bound that its type states" (fun () ->
      expect_proven Fixtures.Prover.callback_whose_type_states_its_allocations);
  Harness.test "the allocations of a callback are not below the bound that its type states"
    (fun () ->
      expect_not_proven
        Fixtures.Prover.callback_whose_type_states_its_allocations_counted_below_its_bound
        "prover.cost");
  Harness.test "a plain bound does not take the amortized time that a callback's type states"
    (fun () ->
      expect_not_proven Fixtures.Prover.callback_whose_type_states_amortized_time "prover.cost");
  Harness.test "an exact bound counts a callback whose type states an exact bound" (fun () ->
      expect_proven Fixtures.Prover.exact_allocations_through_a_callback_with_an_exact_bound);
  Harness.test "an exact bound does not count a callback that is only bounded above" (fun () ->
      List.iter
        (fun text ->
          let actual = read_message text in
          if
            not
              (String.starts_with
                 ~prefix:
                   "Only an upper bound is known for the `allocations` of this call, which may \
                    spend less, so no `==` bound can count it. State the cost with `<=`, or give \
                    the type of the function called an `==` bound."
                 actual)
          then Harness.fail "message %S" actual)
        [
          Fixtures.Prover.exact_allocations_through_a_callback_with_an_upper_bound;
          Fixtures.Prover.exact_allocations_through_a_callback_without_a_bound;
        ]);
  Harness.test "an exact bound that is not met may be above or below the cost" (fun () ->
      let actual = read_message Fixtures.Prover.exact_allocations_that_are_one_short in
      if
        actual
        <> "The function may spend more or less than `cost allocations == 2` states before it \
            returns here. This fails every time the code reaches it."
      then Harness.fail "message %S" actual)

let () =
  let probes =
    Fixtures.Prover.probe_trait_without_a_time_clause
    ^ Fixtures.Prover.probe_impls_with_and_without_an_allocation_bound
  in
  Harness.test "a call through a bound spends the method's allocations" (fun () ->
      expect_proven probes;
      expect_proven
        (probes ^ Fixtures.Prover.probe_each_bounded_by_the_count_times_the_allocations_of_probe));
  Harness.test "two calls through a bound are not within the allocations of one" (fun () ->
      expect_not_proven
        (probes ^ Fixtures.Prover.probe_twice_bounded_by_the_allocations_of_one_probe)
        "prover.cost");
  Harness.test "the allocations of a bound's method are those that the type argument's impl states"
    (fun () -> expect_proven (probes ^ Fixtures.Prover.probe_of_an_impl_with_an_allocation_bound));
  Harness.test "the allocations of a bound's method are unbounded where the impl states none"
    (fun () ->
      expect_not_proven
        (probes ^ Fixtures.Prover.probe_of_an_impl_without_an_allocation_bound)
        "prover.cost");
  Harness.test "a copy through a bound spends the allocations of the copy" (fun () ->
      expect_proven Fixtures.Prover.copy_bounded_by_the_allocations_of_copy);
  Harness.test "two copies through a bound are not within the allocations of one" (fun () ->
      expect_not_proven Fixtures.Prover.copies_bounded_by_the_allocations_of_one_copy "prover.cost")

let () =
  Harness.test
    "the standard combinators pass an allocation bound of zero with lambdas that allocate nothing"
    (fun () -> expect_proven Fixtures.Prover.standard_combinators_under_an_allocation_bound);
  Harness.test "a standard combinator spends the allocations of the lambda it is passed" (fun () ->
      expect_proven Fixtures.Prover.standard_map_of_a_lambda_that_allocates_once;
      expect_not_proven Fixtures.Prover.standard_map_of_a_lambda_that_allocates "prover.cost");
  Harness.test "a collection's map has one output for each element" (fun () ->
      expect_proven Fixtures.Prover.standard_map_keeping_the_length);
  Harness.test "every element that filter or retain keeps satisfies the predicate" (fun () ->
      expect_proven Fixtures.Prover.standard_retain_keeping_only_matches)

let () =
  let ticker = Fixtures.Prover.ticker_without_a_time_clause in
  let probe = Fixtures.Prover.probe_trait_without_a_time_clause in
  Harness.test "a call through a bound of a method without a time clause spends the method's time"
    (fun () ->
      expect_proven (ticker ^ Fixtures.Prover.tick_thrice_bounded_by_the_time_of_tick);
      expect_proven (ticker ^ Fixtures.Prover.relay_bounded_by_the_time_of_its_bounds_tick));
  Harness.test "a loop of calls through a bound spends the method's time once for each call"
    (fun () ->
      expect_proven (probe ^ Fixtures.Prover.probe_each_bounded_by_the_count_times_the_time_of_probe);
      expect_not_proven
        (probe ^ Fixtures.Prover.probe_each_bounded_by_the_time_of_one_probe)
        "prover.cost");
  Harness.test "a call of a method of an associated type's bound spends the method's time"
    (fun () ->
      expect_proven (ticker ^ Fixtures.Prover.movement_ticked_twice_bounded_by_the_time_of_its_tick));
  Harness.test "the time of a bound's method is the time that the type argument's impl states"
    (fun () -> expect_proven (ticker ^ Fixtures.Prover.tick_twice_of_a_countdown_in_constant_time))

let () =
  let list_obligations text =
    let packages = Support.setup [ ("app.main", text) ] in
    let key = List.hd (Support.list_declarations packages (Support.parse_module "app.main")) in
    match
      Support.read_proofs (Support.make_database packages) (Support.parse_file "app.main") key.key
    with
    | Obligations { obligations; _ } -> obligations
    | _ -> Harness.fail "no obligations"
  in
  Harness.test "an untriggered fact that the program writes is named when the solver gives up"
    (fun () ->
      let obligations =
        list_obligations Fixtures.Prover.index_after_a_push_under_an_untriggered_requires
      in
      if
        not
          (List.exists
             (fun (obligation : Prover.Obligation.t) -> obligation.has_untriggered_written_fact)
             obligations)
      then Harness.fail "no obligation names the fact");
  Harness.test "a call in an ensures poses no query for an invariant that the return proved"
    (fun () ->
      let obligations =
        list_obligations
          Fixtures.Prover.ensures_calling_a_predicate_on_a_mut_parameter_with_an_invariant
      in
      if
        List.exists
          (fun (obligation : Prover.Obligation.t) ->
            match obligation.obligation with
            | Invariant_may_fail { moment = When_passed _; _ } -> true
            | _ -> false)
          obligations
      then Harness.fail "the argument's invariant is posed again");
  Harness.test "an untriggered fact of the standard library is not named" (fun () ->
      let obligations = list_obligations Fixtures.Prover.list_index_from_a_map in
      if
        not
          (List.exists
             (fun (obligation : Prover.Obligation.t) -> Logic.has_untriggered_fact obligation.query)
             obligations)
      then Harness.fail "no query has an untriggered fact";
      if
        List.exists
          (fun (obligation : Prover.Obligation.t) -> obligation.has_untriggered_written_fact)
          obligations
      then Harness.fail "an obligation names a fact the program does not write")

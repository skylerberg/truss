let check_file database file =
  match Support.list_diagnostics database file with
  | [] -> Support.list_proof_diagnostics database file
  | errors -> errors

let check packages = check_file (Support.make_database packages)
let expect_proven text = Support.expect_no_diagnostics ~check [ ("app::main", text) ]
let expect_not_proven text code = Support.expect_one_diagnostic ~check text code

let list_codes text =
  let packages = Support.setup [ ("app::main", text) ] in
  Support.list_codes (check packages (Support.parse_file "app::main"))

let expect_only_code text code =
  match list_codes text with
  | [] -> Harness.fail "no diagnostics"
  | actual ->
      if List.exists (fun other -> other <> code) actual then
        Harness.fail "%s" (String.concat ", " actual)

let read_message text =
  let packages = Support.setup [ ("app::main", text) ] in
  match check packages (Support.parse_file "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | actual ->
      Printf.sprintf "%d diagnostics: %s" (List.length actual)
        (String.concat "; " (Support.list_codes actual))

let () =
  Harness.test "an addition that can overflow" (fun () ->
      expect_not_proven Fixtures.Prover.addition_that_can_overflow "prover.overflow");
  Harness.test "an overflow's counterexample names the value" (fun () ->
      let actual = read_message Fixtures.Prover.addition_that_can_overflow in
      if not (String.includes ~affix:"`count` is 255" actual) then Harness.fail "message %S" actual);
  Harness.test "a counterexample names a value that a pattern binds" (fun () ->
      let actual = read_message Fixtures.Prover.increment_of_a_matched_count in
      if not (String.includes ~affix:"`count` is 255" actual) then Harness.fail "message %S" actual);
  Harness.test "a counterexample the solver misses is found in a model of few elements" (fun () ->
      let actual = read_message Fixtures.Prover.addition_under_an_exists_in_a_forall in
      if not (String.includes ~affix:"`value` is 9223372036854775807" actual) then
        Harness.fail "message %S" actual);
  Harness.test "a word count's counterexample names the count" (fun () ->
      let actual = read_message Fixtures.Prover.increment_of_a_word_count in
      if not (String.includes ~affix:"`count` is 9223372036854775807" actual) then
        Harness.fail "message %S" actual);
  Harness.test "a counterexample leaves out the local that a `for` loop introduces" (fun () ->
      let actual = read_message Fixtures.Prover.increment_of_a_word_count in
      if String.includes ~affix:"`position` is" actual then Harness.fail "message %S" actual);
  Harness.test "a counterexample names a local that the code declares" (fun () ->
      let actual = read_message Fixtures.Prover.addition_to_a_local_named_position in
      if not (String.includes ~affix:"`position` is" actual) then Harness.fail "message %S" actual);
  Harness.test "a counterexample leaves out a value that nothing constrains" (fun () ->
      let actual = read_message Fixtures.Prover.increment_under_a_long_name in
      if
        String.includes ~affix:"`name` is" actual
        || not (String.includes ~affix:"`count` is 255" actual)
      then Harness.fail "message %S" actual);
  Harness.test "an obligation with neither a proof nor a counterexample says so" (fun () ->
      let actual = read_message Fixtures.Prover.sum_of_two_cubes in
      if not (String.includes ~affix:"found neither a proof nor a counterexample" actual) then
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
      expect_not_proven Fixtures.Prover.division_by_a_value_that_may_be_zero "prover.division");
  Harness.test "a signed division by -1 can overflow" (fun () ->
      expect_not_proven Fixtures.Prover.signed_division_by_an_unchecked_divisor "prover.overflow");
  Harness.test "a signed division rounds toward zero" (fun () ->
      expect_proven Fixtures.Prover.quotient_ensured_rounded_toward_zero;
      expect_not_proven Fixtures.Prover.quotient_ensured_rounded_down "prover.ensures");
  Harness.test "a remainder has the sign of its left operand" (fun () ->
      expect_proven Fixtures.Prover.remainder_of_negative_seven);
  Harness.test "a shift amount must be less than the width" (fun () ->
      expect_not_proven Fixtures.Prover.shift_by_an_unbounded_amount "prover.shift");
  Harness.test "negating the least signed value overflows" (fun () ->
      expect_not_proven Fixtures.Prover.negation_of_an_int8 "prover.overflow");
  Harness.test "an unreachable that can be reached" (fun () ->
      expect_not_proven Fixtures.Prover.unreachable_that_can_be_reached "prover.unreachable");
  Harness.test "an unreachable after a check" (fun () ->
      expect_proven Fixtures.Prover.unreachable_after_a_check);
  Harness.test "an overflow names `uses Panic` as a way to stop the program" (fun () ->
      let actual = read_message Fixtures.Prover.addition_that_can_overflow in
      if not (String.includes ~affix:"allowed to stop the program with `uses Panic`" actual) then
        Harness.fail "message %S" actual);
  Harness.test "an index that may be out of bounds names `uses Panic` as a way to stop the program"
    (fun () ->
      let actual = read_message Fixtures.Prover.index_that_may_be_out_of_bounds in
      if not (String.includes ~affix:"allowed to stop the program with `uses Panic`" actual) then
        Harness.fail "message %S" actual);
  Harness.test "a function that declares `uses Panic` stops at an operation that fails" (fun () ->
      expect_proven Fixtures.Prover.failing_operations_of_a_function_that_may_panic);
  Harness.test "a lambda proves its operations, since it has no `uses` of its own" (fun () ->
      let actual = read_message Fixtures.Prover.overflow_in_a_lambda_of_a_function_that_may_panic in
      if
        (not (String.includes ~affix:"may overflow `UInt8`" actual))
        || String.includes ~affix:"uses Panic" actual
      then Harness.fail "message %S" actual);
  Harness.test "an overflow in an impl names where the impl can declare `Panic`" (fun () ->
      List.iter
        (fun (text, declaration) ->
          let actual = read_message text in
          if not (String.includes ~affix:("allowed to stop the program with " ^ declaration) actual)
          then Harness.fail "message %S" actual)
        [
          (Fixtures.Prover.increment_in_a_greeter_impl, "`uses Panic` on the `impl`.");
          (Fixtures.Prover.increment_in_a_describe_impl_whose_trait_allows_panic, "`uses Panic`.");
          ( Fixtures.Prover.decrement_in_a_countdown_cursor,
            "`capability Uses = Panic` in the `impl`." );
        ]);
  Harness.test "an overflow in an impl of a trait that fixes its method's capabilities omits Panic"
    (fun () ->
      let actual = read_message Fixtures.Prover.increment_in_a_describe_impl in
      if
        (not (String.includes ~affix:"may overflow `Int64`" actual))
        || String.includes ~affix:"Panic" actual
      then Harness.fail "message %S" actual);
  Harness.test "an index through a bound is proven, since its precondition cannot run" (fun () ->
      expect_not_proven Fixtures.Prover.index_through_a_bound_of_a_function_that_may_panic
        "prover.requires");
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
      expect_not_proven Fixtures.Prover.early_return_of_a_negative "prover.ensures");
  Harness.test "a callee's ensures is a fact after the call" (fun () ->
      expect_proven Fixtures.Prover.bump_ensures_after_the_call);
  Harness.test "a mut argument is mutated only through the callee's ensures" (fun () ->
      expect_not_proven Fixtures.Prover.touch_without_an_ensures "prover.ensures")

let () =
  Harness.test "a loop with an invariant" (fun () ->
      expect_proven Fixtures.Prover.loop_with_an_invariant);
  Harness.test "a loop invariant that an iteration breaks" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_breaking_its_invariant "prover.invariant");
  Harness.test "a loop in a function with a time clause must end" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_under_a_finite_time_clause "prover.termination");
  Harness.test "a loop that counts up to its bound ends" (fun () ->
      expect_proven Fixtures.Prover.while_loop_counting_up);
  Harness.test "a for loop over a range knows its index is in range" (fun () ->
      expect_proven Fixtures.Prover.range_index_plus_one);
  Harness.test "recursion that decreases" (fun () ->
      expect_proven Fixtures.Prover.recursion_that_decreases);
  Harness.test "recursion that does not decrease" (fun () ->
      expect_not_proven Fixtures.Prover.recursion_that_does_not_decrease "prover.termination");
  Harness.test "a contract that calls its own function applies the function's limited copy"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Prover.recursive_total_in_its_own_contract) ]
      in
      let caller =
        List.hd (Support.list_declarations packages (Support.parse_module "app::main"))
      in
      let rec applies_limited (term : Logic.term) =
        match term with
        | Apply (Limited _, _) -> true
        | Apply (_, terms) | Operation (_, terms) -> List.exists applies_limited terms
        | Is (_, term) | Exists (_, term) -> applies_limited term
        | Forall (_, triggers, body) -> List.exists applies_limited (body :: triggers)
        | Symbol _ | Integer _ | Boolean _ | Bits _ -> false
      in
      match
        Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
          (Resolve.Names.make_key caller)
      with
      | Obligations { obligations = [ obligation ]; _ } ->
          if not (List.exists applies_limited obligation.query.facts) then
            Harness.fail "no fact applies the limited copy: %s" (Logic.show_query obligation.query)
      | _ -> Harness.fail "expected one obligation")

let () =
  Harness.test "mutual recursion without measures cannot be shown to end" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Prover.even_and_odd_without_measures) ]
      in
      match Support.list_codes (check packages (Support.parse_file "app::main")) with
      | [ "prover.termination"; "prover.termination" ] -> ()
      | codes -> Harness.fail "codes %s" (String.concat ", " codes));
  Harness.test "mutual recursion that decreases" (fun () ->
      expect_proven Fixtures.Prover.even_and_odd_with_measures);
  Harness.test "an impl that reaches itself through a generic function cannot be shown to end"
    (fun () ->
      expect_only_code Fixtures.Prover.check_reaching_itself_through_a_generic "prover.termination")

let () =
  Harness.test "a proof that reads a contract that fails to check is blocked and reports nothing"
    (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Prover.caller_of_double);
            ("app::main/broken", Fixtures.Prover.double_with_an_ill_typed_ensures);
          ]
      in
      let main = Support.parse_file "app::main" in
      (match
         Support.list_codes (Support.list_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller does not check: %s" (String.concat ", " codes));
      (match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the blocked proof reports %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.path (Support.make_top_path "app::main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app::main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          (Resolve.Names.make_key caller)
      with
      | Some Blocked -> ()
      | Some (Value _ | Failed _) -> Harness.fail "the proof is computed"
      | None -> Harness.fail "the caller has no proof")

let () =
  Harness.test "a type error in a callee's body blocks no caller's proof" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Prover.caller_of_double);
            ("app::main/double", Fixtures.Prover.double_with_an_ill_typed_body);
          ]
      in
      let main = Support.parse_file "app::main" in
      (match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller's proof reports %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.path (Support.make_top_path "app::main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app::main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          (Resolve.Names.make_key caller)
      with
      | Some (Value (Obligations _)) -> ()
      | Some (Value (Unsupported _ | Not_proven_here)) ->
          Harness.fail "the caller has no obligations"
      | Some (Failed _ | Blocked) -> Harness.fail "the proof is blocked"
      | None -> Harness.fail "the caller has no proof");
  Harness.test "a body that calls a broken signature blocks no caller's proof" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Prover.caller_of_double);
            ("app::main/double", Fixtures.Prover.double_reading_a_secret);
          ]
      in
      let main = Support.parse_file "app::main" in
      (match
         Support.list_codes (Support.list_proof_diagnostics (Support.make_database packages) main)
       with
      | [] -> ()
      | codes -> Harness.fail "the caller's proof reports %s" (String.concat ", " codes));
      let caller =
        List.find
          (fun (declaration : Resolve.Names.declaration) ->
            Path.equal declaration.path (Support.make_top_path "app::main" "caller"))
          (Support.list_declarations packages (Support.parse_module "app::main"))
      in
      match
        Database.For_testing.find_proof
          (Support.prove (Support.make_database packages) main)
          (Resolve.Names.make_key caller)
      with
      | Some (Value (Obligations _)) -> ()
      | Some (Value (Unsupported _ | Not_proven_here)) ->
          Harness.fail "the caller has no obligations"
      | Some (Failed _ | Blocked) -> Harness.fail "the proof is blocked"
      | None -> Harness.fail "the caller has no proof")

let () =
  Harness.test "a broken method of a trait blocks no call of its other methods" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Prover.total_of_a_box_size);
            ("app::main/measured", Fixtures.Prover.measured_trait_with_a_broken_method);
          ]
      in
      let database = Support.make_database packages in
      let main = Support.parse_file "app::main" in
      (match
         Support.list_codes
           (Support.list_diagnostics database (Support.parse_file "app::main/measured"))
       with
      | [ "resolve.unknown_name" ] -> ()
      | codes -> Harness.fail "the trait reports %s" (String.concat ", " codes));
      (match Support.list_codes (Support.list_diagnostics database main) with
      | [] -> ()
      | codes -> Harness.fail "a caller does not check: %s" (String.concat ", " codes));
      (match Support.list_codes (Support.list_proof_diagnostics database main) with
      | [] -> ()
      | codes -> Harness.fail "a caller's proof reports %s" (String.concat ", " codes));
      let proofs = Support.prove database main in
      List.iter
        (fun (declaration : Resolve.Names.declaration) ->
          match Database.For_testing.find_proof proofs (Resolve.Names.make_key declaration) with
          | Some (Value (Obligations _)) -> ()
          | Some (Value (Unsupported _ | Not_proven_here)) ->
              Harness.fail "%s has no obligations" (Path.show declaration.path)
          | Some (Failed _ | Blocked) ->
              Harness.fail "the proof of %s is blocked" (Path.show declaration.path)
          | None -> Harness.fail "%s has no proof" (Path.show declaration.path))
        ((Support.make_names packages main.module_.package).list_declarations_in main))

let tree = Fixtures.Prover.tree

let () =
  Harness.test "recursion on a part of a parameter ends" (fun () ->
      expect_proven (tree ^ Fixtures.Prover.leftmost));
  Harness.test "recursion on the parameter itself does not end" (fun () ->
      expect_not_proven (tree ^ Fixtures.Prover.spin_on_its_tree) "prover.termination");
  Harness.test "a match with guards ends in an unreachable that is proven" (fun () ->
      expect_proven Fixtures.Prover.match_with_exhaustive_guards;
      expect_not_proven Fixtures.Prover.match_with_guards_missing_zero "prover.unreachable")

let () =
  Harness.test "a theorem the solver proves alone" (fun () ->
      expect_proven Fixtures.Prover.squares_grow);
  Harness.test "a quantifier over a range" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_an_inclusive_range "prover.ensures");
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
      expect_not_proven (shape ^ Fixtures.Prover.circle_radius_squared) "prover.overflow");
  Harness.test "a counterexample shows a variant by its name" (fun () ->
      let actual = read_message (shape ^ Fixtures.Prover.circle_radius_plus_one) in
      if not (String.includes ~affix:"`shape` is Circle(radius: 9223372036854775807)" actual) then
        Harness.fail "message %S" actual);
  Harness.test "a requires can match on a parameter" (fun () ->
      expect_proven (shape ^ Fixtures.Prover.requires_matching_a_shape));
  Harness.test "with replaces one field and keeps the others" (fun () ->
      expect_proven (point ^ Fixtures.Prover.point_with_x_incremented));
  Harness.test "derived equality is the solver's equality" (fun () ->
      expect_proven (point ^ Fixtures.Prover.point_rebuilt_equals_itself));
  Harness.test "is binds the parts it matches, where it is true" (fun () ->
      expect_proven Fixtures.Prover.is_some_positive);
  Harness.test "? continues with the value inside" (fun () ->
      expect_not_proven Fixtures.Prover.question_mark_on_an_option "prover.overflow");
  Harness.test "? returns an error unchanged" (fun () ->
      expect_proven Fixtures.Prover.question_mark_on_a_result)

let () =
  Harness.test "an index must be in bounds" (fun () ->
      expect_not_proven Fixtures.Prover.index_without_a_bound "prover.requires");
  Harness.test "an index the requires bounds" (fun () ->
      expect_proven Fixtures.Prover.index_bounded_by_the_requires);
  Harness.test "an index a range loop bounds" (fun () ->
      expect_proven Fixtures.Prover.saturating_sum_over_a_range);
  Harness.test "assigning to an element checks its index" (fun () ->
      expect_not_proven Fixtures.Prover.element_assigned_without_a_bound "prover.requires");
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
        "prover.requires")

let each_index = Fixtures.Prover.each_index

let () =
  Harness.test "a lambda's body is proven where it is written" (fun () ->
      expect_not_proven Fixtures.Prover.apply_of_an_overflowing_lambda "prover.overflow");
  Harness.test "a lambda may rely on its callee's promise about its arguments" (fun () ->
      expect_proven (each_index ^ Fixtures.Prover.each_index_reading_items));
  Harness.test "a lambda without such a promise knows nothing of its arguments" (fun () ->
      expect_not_proven Fixtures.Prover.each_without_a_promise "prover.requires");
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
  Harness.test "a lending method that lends a part it does not promise" (fun () ->
      expect_not_proven Fixtures.Prover.couple_larger_lending_first "prover.ensures");
  Harness.test "a loop over a user's collection gets the facts of its `count` and its `element`"
    (fun () -> expect_proven (couple ^ Fixtures.Prover.couple_loop_counted));
  Harness.test
    "the elements that a loop has read meet the postcondition of the collection's `element`"
    (fun () -> expect_proven (couple ^ Fixtures.Prover.couple_loop_with_known_elements));
  Harness.test "the elements that a loop has read are not known beyond that postcondition"
    (fun () ->
      expect_not_proven
        (couple ^ Fixtures.Prover.couple_loop_with_one_known_element)
        "prover.invariant");
  Harness.test "a loop that mutates a collection's elements must keep their count" (fun () ->
      expect_not_proven Fixtures.Prover.row_loop_changing_counts "prover.invariant");
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
  Harness.test "a loop over a cursor in a field calls its next" (fun () ->
      expect_proven Fixtures.Prover.countdown_in_a_field);
  Harness.test "a loop over a cursor counts a body that calls an amortized callee" (fun () ->
      expect_proven Fixtures.Prover.spaced_characters);
  (let samples = Fixtures.Prover.samples in
   Harness.test "an assignment through an index is to a key the collection accepts" (fun () ->
       expect_proven (samples ^ Fixtures.Prover.samples_stored_within_bounds));
   Harness.test "an assignment through an index to a key the collection does not accept" (fun () ->
       expect_not_proven
         (samples ^ Fixtures.Prover.samples_stored_without_a_bound)
         "prover.requires"));
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
    \    cost time finite\n\
    \  {\n\
    \    Flag(on: %s)\n\
    \  }\n\n\
    \  fn combine(self, other: Flag) -> Flag\n\
    \    ensures result == Flag(on: self.on || other.on)\n\
    \    cost time finite\n\
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
  Harness.test "building a value must meet its invariant" (fun () ->
      expect_not_proven (span ^ Fixtures.Prover.span_built_without_its_invariant) "prover.invariant");
  Harness.test "building a value that meets its invariant" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_built_within_its_invariant));
  Harness.test "a derived Default must meet the invariant" (fun () ->
      expect_not_proven Fixtures.Prover.positive_default "prover.invariant");
  Harness.test "a derived Default built from field defaults meets the invariant" (fun () ->
      expect_proven Fixtures.Prover.positive_default_from_field_defaults);
  Harness.test "a field's default must meet its type's invariant" (fun () ->
      expect_not_proven Fixtures.Prover.holder_defaulting_to_an_invalid_positive "prover.invariant");
  Harness.test "a parameter meets its invariant" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_parameter_ensured_ordered));
  Harness.test "a mut parameter must meet its invariant when the function returns" (fun () ->
      expect_not_proven (span ^ Fixtures.Prover.span_high_assigned_below_low) "prover.invariant");
  Harness.test "a body may break an invariant between calls" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_low_assigned_above_high));
  Harness.test "a value passed to a call must meet its invariant" (fun () ->
      expect_not_proven
        (span ^ Fixtures.Prover.span_passed_after_breaking_its_invariant)
        "prover.invariant");
  Harness.test "a private method that takes mut self is a step of an update" (fun () ->
      expect_proven (span ^ Fixtures.Prover.span_restore))

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
      expect_not_proven Fixtures.Prover.array_index_at_its_count "prover.requires");
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
  Harness.test "a bitwise fact that does not hold has a counterexample" (fun () ->
      expect_not_proven Fixtures.Prover.low_bit_ensured_zero "prover.ensures")

let () =
  Harness.test "a slice's elements are its collection's, from its start" (fun () ->
      expect_proven Fixtures.Prover.slice_element_read);
  Harness.test "a list passed as a slice is a view with its model" (fun () ->
      expect_proven Fixtures.Prover.count_of_a_list_as_a_slice);
  Harness.test "a slice must be within its collection" (fun () ->
      expect_not_proven Fixtures.Prover.slice_past_the_end "prover.requires");
  Harness.test "two slices lent together must not overlap" (fun () ->
      expect_not_proven Fixtures.Prover.both_of_overlapping_slices "prover.disjoint");
  Harness.test "two halves of a list can be lent together" (fun () ->
      expect_proven Fixtures.Prover.both_halves_of_a_list)

let () =
  Harness.test "a string literal's length is its bytes'" (fun () ->
      expect_proven Fixtures.Prover.length_of_a_string_with_an_accent);
  Harness.test "a long string literal has its length without a fact for each byte" (fun () ->
      expect_proven Fixtures.Prover.length_of_a_long_string_literal);
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
  Harness.test "a call of from_template through a bound cannot see the tag's requires" (fun () ->
      expect_not_proven Fixtures.Prover.from_template_through_a_bound "prover.requires");
  Harness.test "a tagged template that does not meet its tag's requires" (fun () ->
      expect_not_proven (shout ^ Fixtures.Prover.shout_of_a_copied_name) "prover.requires")

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
      expect_not_proven Fixtures.Prover.float_points_equal_and_identical "prover.ensures");
  Harness.test "a float counterexample is written as Truss writes floats" (fun () ->
      let actual = read_message Fixtures.Prover.float_times_zero in
      if not (String.includes ~affix:"infinity" actual || String.includes ~affix:"NaN" actual) then
        Harness.fail "message %S" actual)

let dice = Fixtures.Prover.dice

let () =
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
  Harness.test "a map literal holds each key's value" (fun () ->
      expect_proven Fixtures.Prover.map_literal_read);
  Harness.test "a map literal's keys must be distinct" (fun () ->
      expect_not_proven Fixtures.Prover.map_literal_with_a_repeated_key "prover.requires");
  Harness.test "a set literal contains its listed elements and nothing else" (fun () ->
      expect_proven Fixtures.Prover.set_literal_contains);
  Harness.test "any is one allocation" (fun () ->
      expect_proven Fixtures.Prover.any_of_a_value_with_one_allocation);
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
  Harness.test "a quantifier's pattern leaves out the elements it does not match" (fun () ->
      expect_proven Fixtures.Prover.specification_quantifier_with_a_refutable_pattern);
  Harness.test "a quantifier over a range value reads the range's `count` and `element`" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_a_range_value);
  Harness.test "a quantifier in a body over a set reaches every member of the set" (fun () ->
      expect_proven Fixtures.Prover.quantifier_over_set_members_in_a_body)

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
      expect_not_proven (swap ^ Fixtures.Prover.exchange_of_two_elements) "prover.disjoint");
  Harness.test "two different elements can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_distinct_elements));
  Harness.test "elements of two ranges lent together must be in ranges that do not overlap"
    (fun () ->
      expect_not_proven
        (swap ^ Fixtures.Prover.exchange_of_elements_of_overlapping_ranges)
        "prover.disjoint");
  Harness.test "elements of two ranges that do not overlap can be lent together" (fun () ->
      expect_proven (swap ^ Fixtures.Prover.exchange_of_elements_of_disjoint_ranges));
  Harness.test "an element of a range lent `mut` must not be the element that an argument views"
    (fun () ->
      expect_not_proven Fixtures.Prover.element_of_a_range_pushed_onto_itself "prover.disjoint");
  Harness.test "parallel branches that mutate elements must mutate different ones" (fun () ->
      expect_not_proven Fixtures.Prover.parallel_branches_assigning_two_elements "prover.disjoint")

let () =
  Harness.test "self mutated on one path is joined with the other" (fun () ->
      expect_not_proven Fixtures.Prover.box_set_on_one_path "prover.ensures");
  Harness.test "a lending method's `ensures` holds for the part lent on each path" (fun () ->
      expect_not_proven Fixtures.Prover.maybe_part_lent_on_each_path "prover.ensures")

let () =
  Harness.test "a loop forgets a list it mutates through a method" (fun () ->
      expect_not_proven Fixtures.Prover.loop_pushing_onto_a_list "prover.assertion");
  Harness.test "a loop forgets a record whose field it assigns" (fun () ->
      expect_not_proven Fixtures.Prover.loop_assigning_a_box_field "prover.assertion");
  Harness.test "a loop forgets self when it mutates it" (fun () ->
      expect_not_proven Fixtures.Prover.box_fill_loop "prover.assertion");
  Harness.test "a loop forgets a place that it provides `mut`" (fun () ->
      expect_not_proven Fixtures.Prover.marker_provided_mut_in_a_loop "prover.assertion")

let constant_step = Fixtures.Prover.constant_step

let () =
  Harness.test "a body with no calls is O(1)" (fun () ->
      expect_proven Fixtures.Prover.constant_body_of_time_o_1);
  Harness.test "calls to O(1) functions are O(1)" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.step_of_a_step));
  Harness.test "a call to a function with no bound on its time" (fun () ->
      expect_not_proven Fixtures.Prover.call_of_a_finite_time_callee "prover.cost");
  Harness.test "a loop over a range is linear" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.range_loop_of_linear_time));
  Harness.test "a loop over a range is not constant" (fun () ->
      expect_not_proven (constant_step ^ Fixtures.Prover.range_loop_of_constant_time) "prover.cost");
  Harness.test "nested loops over ranges are quadratic" (fun () ->
      expect_proven (constant_step ^ Fixtures.Prover.nested_range_loops_of_quadratic_time));
  Harness.test "a loop whose iterations cost their index is quadratic" (fun () ->
      expect_proven Fixtures.Prover.work_with_iterations_costing_their_index);
  Harness.test "a loop over a list runs once per element" (fun () ->
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
  Harness.test "nested loops are not linear" (fun () ->
      expect_not_proven
        (constant_step ^ Fixtures.Prover.nested_range_loops_ensured_linear)
        "prover.cost");
  Harness.test "two recursive calls on one less are not linear" (fun () ->
      expect_not_proven Fixtures.Prover.two_recursive_calls_on_one_less "prover.cost");
  Harness.test "functions in a cycle that branch are not linear" (fun () ->
      expect_not_proven Fixtures.Prover.branching_ping_and_pong "prover.cost");
  Harness.test "a callback's time is not free" (fun () ->
      expect_not_proven Fixtures.Prover.each_visiting_a_finite_callback "prover.cost");
  Harness.test "calls through a lambda that captures the function value are not known" (fun () ->
      expect_not_proven Fixtures.Prover.each_visiting_through_a_capturing_lambda "prover.cost");
  Harness.test "a quantifier over a costly body is not linear" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_a_spinning_body "prover.cost");
  Harness.test "a loop's cost clause that is too small" (fun () ->
      expect_not_proven Fixtures.Prover.while_loop_with_a_small_cost_clause "prover.cost");
  Harness.test "calls of a capability's method are counted" (fun () ->
      expect_proven Fixtures.Prover.meter_ticks_counted);
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
  Harness.test "a potential below zero" (fun () ->
      expect_not_proven "type Debt(owed: Int64)\n  cost potential owed\n" "prover.cost");
  Harness.test "a potential its invariant keeps at or above zero" (fun () ->
      expect_proven Fixtures.Prover.debt_potential)

let count_holes text =
  let packages = Support.setup [ ("app::main", text) ] in
  let prove_key =
    Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
  in
  List.fold_left
    (fun total declaration ->
      match prove_key (Resolve.Names.make_key declaration) with
      | Obligations outcome -> total + List.length outcome.holes
      | Unsupported _ | Not_proven_here -> total)
    0
    (Support.list_declarations packages (Support.parse_module "app::main"))

let () =
  Harness.test "a todo in a theorem is a hole, not a failure" (fun () ->
      let text = Fixtures.Prover.theorem_of_todo in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "a todo in a proof block leaves the rest of its path to it" (fun () ->
      let text = Fixtures.Prover.proof_block_of_todo in
      expect_proven text;
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "a contract on a body that is not written waits for it, and is no hole" (fun () ->
      let text = Fixtures.Prover.todo_body_with_an_ensures in
      expect_proven text;
      if count_holes text <> 0 then Harness.fail "%d holes" (count_holes text));
  Harness.test "the code before a todo is still proven" (fun () ->
      expect_not_proven Fixtures.Prover.element_read_before_a_todo "prover.requires");
  Harness.test "a constant, a field default, or a parameter default left todo is read" (fun () ->
      expect_proven Fixtures.Prover.values_left_todo);
  Harness.test "a constant left todo has an unknown value" (fun () ->
      expect_not_proven Fixtures.Prover.increment_of_a_todo_constant "prover.overflow");
  Harness.test "an impl's laws wait while one of its methods is not written" (fun () ->
      expect_proven Fixtures.Prover.meters_equal_left_todo);
  Harness.test "a type that contains itself through a map's values is read" (fun () ->
      expect_proven Fixtures.Prover.tree_of_maps)

let () =
  Harness.test "a lambda's result is in range only for arguments in range" (fun () ->
      expect_not_proven Fixtures.Prover.same_lambda_in_range "prover.ensures");
  Harness.test "an uncalled lambda's calls show nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.lambda_calling_a_hang_uncalled "prover.ensures");
  Harness.test "a lambda whose arguments cannot meet its requires shows nothing of the path"
    (fun () ->
      expect_not_proven Fixtures.Prover.each_index_with_an_unreachable_lambda "prover.ensures");
  Harness.test "a quantifier over an empty range shows nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.quantifier_over_an_empty_range_after_a_hang "prover.ensures");
  Harness.test "a lambda over a type no value has shows nothing of the path" (fun () ->
      expect_not_proven Fixtures.Prover.lambda_over_an_empty_type "prover.ensures");
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
      if count_holes text <> 1 then Harness.fail "%d holes" (count_holes text));
  Harness.test "a law whose proof holds a todo is a hole where it is assumed" (fun () ->
      let text = Fixtures.Prover.zero_law_with_a_todo_proof in
      if count_holes text <> 2 then Harness.fail "%d holes" (count_holes text));
  Harness.test "each impl of a trait with arguments keeps its own laws" (fun () ->
      expect_not_proven Fixtures.Prover.scale_impls_with_their_own_laws "prover.law");
  Harness.test "an element mutated through a lend meets its invariant when the lend ends" (fun () ->
      expect_not_proven Fixtures.Prover.span_low_raised_through_a_lend "prover.invariant");
  Harness.test "an element mutated through a lend that keeps its invariant proves" (fun () ->
      expect_proven Fixtures.Prover.span_high_raised_through_a_lend);
  Harness.test "a lent part meets its invariant" (fun () ->
      expect_not_proven Fixtures.Prover.positive_lent_by_a_source "prover.invariant");
  Harness.test "a loop keeps the validity of each value it mutates" (fun () ->
      expect_proven Fixtures.Prover.positive_reassigned_in_a_loop);
  Harness.test "an iteration must keep the validity of each value the loop mutates" (fun () ->
      expect_not_proven Fixtures.Prover.positive_zeroed_in_a_loop "prover.invariant")

let () =
  Harness.test "a mut slice's bounds are evaluated once" (fun () ->
      expect_not_proven Fixtures.Prover.mut_slice_with_counted_bounds "prover.ensures");
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
      expect_not_proven Fixtures.Prover.below_three_bound_to_a_local "prover.requires");
  Harness.test "a function with a requires passed through a local must accept every argument"
    (fun () -> expect_not_proven Fixtures.Prover.below_one_passed_through_a_local "prover.requires");
  Harness.test "a callback's requires names a mut parameter as the caller passed it" (fun () ->
      expect_not_proven Fixtures.Prover.callback_requires_naming_a_mut_limit "prover.requires");
  Harness.test "a forwarded callback must be promised its requires" (fun () ->
      expect_not_proven Fixtures.Prover.callback_forwarded_without_its_requires "prover.requires");
  Harness.test "a call through a function value gives a valid result" (fun () ->
      expect_proven Fixtures.Prover.positive_made_by_a_function_value);
  Harness.test "a lambda returns a valid value" (fun () ->
      expect_not_proven Fixtures.Prover.apply_of_a_positive_lambda "prover.invariant");
  Harness.test "a callback with a requires bound to a local must accept every argument" (fun () ->
      expect_not_proven Fixtures.Prover.callback_with_a_requires_bound_to_a_local "prover.requires")

let () =
  Harness.test "provided methods that call each other are recursion" (fun () ->
      expect_only_code Fixtures.Prover.ping_and_pong_provided_methods "prover.termination");
  Harness.test "an implementation that calls the function providing it is recursion" (fun () ->
      expect_only_code Fixtures.Prover.looper_provided_by_its_own_caller "prover.termination");
  Harness.test "a call through any that reaches back is recursion" (fun () ->
      expect_only_code Fixtures.Prover.step_reaching_back_through_any "prover.termination");
  Harness.test "a method that calls itself through any is recursion" (fun () ->
      expect_not_proven Fixtures.Prover.check_calling_itself_through_any "prover.termination")

let () =
  Harness.test "a constant's value is well defined" (fun () ->
      expect_not_proven "let shifted: UInt8 = 1 << 8\n" "prover.shift");
  Harness.test "a constant whose value is in range proves" (fun () ->
      expect_proven "let shifted: UInt8 = 1 << 7\n")

let () =
  Harness.test "generic negation needs the trait method's precondition" (fun () ->
      expect_not_proven Fixtures.Prover.generic_negation "prover.requires");
  Harness.test "generic negation proves where the trait method's precondition holds" (fun () ->
      expect_proven Fixtures.Prover.generic_negation_with_its_precondition);
  Harness.test
    "a function with a time clause converts, makes a default, and indexes through a bound"
    (fun () ->
      expect_proven Fixtures.Prover.conversions_and_indexing_through_bounds_under_a_time_clause)

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

let check_across library program =
  let packages =
    Support.setup
      ~dependencies:[ ("app", "lib") ]
      [ ("lib::numbers", library); ("app::main", "use lib::numbers\n\n" ^ program) ]
  in
  check packages (Support.parse_file "app::main")

let public_doubling =
  "public fn double(limit_count: Int64) -> Int64\n\
  \  requires limit_count < 1000 && limit_count > -1000\n\
  \  ensures result == limit_count * 2\n\
  \  cost time O(1)\n\
   {\n\
  \  limit_count * 2\n\
   }\n"

let () =
  Harness.test "a caller in another package reads its callee's contract" (fun () ->
      match check_across public_doubling Fixtures.Prover.twice_through_another_packages_double with
      | [] -> ()
      | actual ->
          Harness.fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)))

let () =
  Harness.test
    "a recursive function proves a plain and an amortized bound, each by its own counting"
    (fun () -> expect_proven Fixtures.Prover.shift_left_all)

let () =
  Harness.test "a callee's clause in another file is named by its file and line" (fun () ->
      let actual = read_message Fixtures.Prover.first_element_of_a_list in
      if
        not
          (String.includes ~affix:"The clause that must hold is at `standard/list/list.truss:"
             actual)
      then Harness.fail "message %S" actual)

let () =
  Harness.test "an insertion into a set of integers is amortized in its length" (fun () ->
      expect_proven Fixtures.Prover.integer_set_add);
  Harness.test "an insertion into a set of any elements is amortized in their comparisons"
    (fun () -> expect_proven Fixtures.Prover.generic_set_add);
  Harness.test "a list filled with integers is linear in its count" (fun () ->
      expect_proven Fixtures.Prover.zeros_filled)

let () =
  Harness.test "a callee's requires about the caller's parameters is offered as the caller's"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Prover.halve_of_an_unbounded_parameter) ]
      in
      match check packages (Support.parse_file "app::main") with
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
      expect_proven Fixtures.Prover.counted_up_under_a_quantifier)

let () =
  Harness.test "a concurrent for may return early, with a value known by its type" (fun () ->
      expect_proven Fixtures.Prover.any_negative_through_a_concurrent_for);
  Harness.test "a value returned from a concurrent for is not known to be any one iteration's"
    (fun () -> expect_not_proven Fixtures.Prover.claimed_through_a_concurrent_for "prover.ensures")

let () =
  let fix_titles text =
    let packages = Support.setup [ ("app::main", text) ] in
    List.concat_map
      (fun (diagnostic : Diagnostic.t) ->
        List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes)
      (check packages (Support.parse_file "app::main"))
  in
  Harness.test "an impl's method offers no requires, since the trait's would have to imply it"
    (fun () ->
      List.iter
        (fun text ->
          match fix_titles text with
          | [] -> ()
          | actual -> Harness.fail "%s" (String.concat "; " actual))
        [
          Fixtures.Prover.increment_in_a_describe_impl;
          Fixtures.Prover.increment_in_a_greeter_impl;
          Fixtures.Prover.decrement_in_a_countdown_cursor;
        ]);
  Harness.test "a divisor that may be zero offers a requires that it is not" (fun () ->
      match fix_titles Fixtures.Prover.halves_of_an_unchecked_divisor with
      | [ "Add `requires parts != 0`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a shift amount that may be too large offers a requires below the width" (fun () ->
      match fix_titles Fixtures.Prover.shifted_by_an_unbounded_amount with
      | [ "Add `requires by < 64`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an overflow with a literal offers the bound as a requires" (fun () ->
      let packages = Support.setup [ ("app::main", Fixtures.Prover.next_count) ] in
      match check packages (Support.parse_file "app::main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count <= UInt8.maximum - 1`"
        ->
          ()
      | actual ->
          Harness.fail "%s"
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    String.concat ", "
                      (List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes))
                  actual)));
  Harness.test "a failed assert about the parameters offers it as a requires" (fun () ->
      match fix_titles Fixtures.Prover.assert_on_ordered_parameters with
      | [ "Add `requires low < high`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a failed assert under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.assert_under_an_if with
      | [ "Add `requires (flag) ==> (count > 0)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a failed assert with arithmetic offers it as a requires" (fun () ->
      match fix_titles Fixtures.Prover.assert_on_spaced_parameters with
      | [ "Add `requires low + 2 * high <= 100 - (high - low)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an overflow of a local offers the bound on the parameter it holds" (fun () ->
      match fix_titles Fixtures.Prover.bumped_local with
      | [ "Add `requires start <= Int64.maximum - 1`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a callee's requires through a local names the caller's parameter" (fun () ->
      match fix_titles Fixtures.Prover.halve_of_a_local with
      | [ "Add `requires total < 100`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an unsigned sum that may overflow offers only its upper bound" (fun () ->
      match fix_titles Fixtures.Prover.total_of_two_bytes with
      | [ "Add `requires count + other <= UInt8.maximum`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an unsigned difference that may overflow offers only its lower bound" (fun () ->
      match fix_titles Fixtures.Prover.gap with
      | [ "Add `requires 0 <= high - low`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a signed product that may overflow offers both limits by name" (fun () ->
      match fix_titles Fixtures.Prover.scaled_count with
      | [ "Add `requires Int64.minimum <= count * 1000 && count * 1000 <= Int64.maximum`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an overflow under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.product_under_an_if with
      | [
       "Add `requires (flag) ==> (Int64.minimum <= left * right && left * right <= Int64.maximum)`";
      ] ->
          ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a negation that may overflow offers to exclude the least value" (fun () ->
      match fix_titles Fixtures.Prover.negated_value with
      | [ "Add `requires value != Int64.minimum`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a signed quotient that may overflow offers to exclude the least value over -1"
    (fun () ->
      match fix_titles Fixtures.Prover.signed_quotient with
      | [ "Add `requires dividend != Int64.minimum || divisor != -1`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "an overflow with a literal under an if offers the if's condition as a premise"
    (fun () ->
      match fix_titles Fixtures.Prover.next_count_under_an_if with
      | [ "Add `requires (flag) ==> (count <= UInt8.maximum - 1)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a divisor under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.divisor_under_an_if with
      | [ "Add `requires (flag) ==> (parts != 0)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a shift amount under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.shift_under_an_if with
      | [ "Add `requires (flag) ==> (by < 64)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a callee's requires under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.call_under_an_if with
      | [ "Add `requires (flag) ==> (count < 100)`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a condition with no spelling in the parameters leaves the requires unconditional"
    (fun () ->
      match fix_titles Fixtures.Prover.next_count_under_a_quotient with
      | [ "Add `requires count <= UInt8.maximum - 1`" ] -> ()
      | actual -> Harness.fail "%s" (String.concat "; " actual));
  Harness.test "a failed assert about a call's result offers no requires" (fun () ->
      let packages = Support.setup [ ("app::main", Fixtures.Prover.assert_on_a_list_length) ] in
      match check packages (Support.parse_file "app::main") with
      | [ { code; fixes = []; _ } ] when Diagnostic.Code.name code = "prover.assertion" -> ()
      | actual -> Harness.fail "%d diagnostics" (List.length actual));
  Harness.test "an overflow names the fixes that change the code's semantics" (fun () ->
      let actual = read_message Fixtures.Prover.next_count in
      if not (String.includes ~affix:"checked operation" actual) then
        Harness.fail "message %S" actual)

let () =
  Harness.test "a counterexample says which way each if on its path goes" (fun () ->
      let actual = read_message Fixtures.Prover.step_up_or_down in
      if not (String.includes ~affix:"On that path, `up` is true, `count > 100` is true." actual)
      then Harness.fail "message %S" actual);
  Harness.test "a counterexample says which arm of a match its path takes" (fun () ->
      let actual = read_message Fixtures.Prover.bump_of_an_option in
      if not (String.includes ~affix:"On that path, the arm `Some(count)` is taken." actual) then
        Harness.fail "message %S" actual)

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
  Harness.test "a contract with branches, called under a quantifier on no bound value, holds there"
    (fun () -> expect_proven Fixtures.Prover.used_bits_under_a_quantifier);
  Harness.test "a derived ordering of a one-field record is its field's, for every value" (fun () ->
      expect_proven Fixtures.Prover.day_ordering_theorem);
  Harness.test "a derived ordering compares fields in order, for every value" (fun () ->
      expect_proven Fixtures.Prover.pair_ordering_theorem)

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
      let packages = Support.setup [ ("app::main", text) ] in
      match check packages (Support.parse_file "app::main") with
      | [ ({ notes = [ (cited, _) ]; _ } : Diagnostic.t) ] ->
          let quoted = String.sub text cited.start (cited.stop - cited.start) in
          if not (String.includes ~affix:"(bits & 15) < 8" quoted) then
            Harness.fail "cites %S" quoted
      | actual -> Harness.fail "%s" (String.concat ", " (Support.list_codes actual)))

let make_early_return_source ensures =
  "fn f(first: mut Int64, second: mut Int64) -> Int64\n  requires second < 100\n" ^ ensures
  ^ "  uses Tasks\n{\n  concurrent {\n    return 0\n    second += 1\n  }\n}\n"

let () =
  Harness.test "an early exit from a concurrent block waits for the other branches" (fun () ->
      expect_proven (make_early_return_source "  ensures second == old(second) + 1\n"));
  Harness.test "an early exit from a concurrent block sees the other branches' mutations" (fun () ->
      expect_not_proven
        (make_early_return_source "  ensures second == old(second)\n")
        "prover.ensures");
  Harness.test "a concurrent block with no early exit is read as its branches in order" (fun () ->
      expect_proven Fixtures.Prover.concurrent_block_bumping_two_counts)

let () =
  Harness.test "a counterexample gives the values of the locals where it fails" (fun () ->
      let text = read_message Fixtures.Prover.element_read_at_a_branch_local in
      if not (String.includes ~affix:"`at` is" text) then Harness.fail "%s" text);
  Harness.test "a file's proof states list proven and unproven obligations" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Prover.element_sum_with_one_unchecked_index) ]
      in
      let states =
        Support.list_proof_states (Support.make_database packages) (Support.parse_file "app::main")
      in
      let failed =
        List.filter (fun (state : Source.span Prover.state) -> state.failure <> None) states
      in
      if List.length failed <> 1 || List.length states < 2 then
        Harness.fail "%d states, %d failed" (List.length states) (List.length failed));
  Harness.test "a call's requires that may not hold has a note at the clause" (fun () ->
      let text = Fixtures.Prover.halved_of_an_unchecked_count in
      let packages = Support.setup [ ("app::main", text) ] in
      match check packages (Support.parse_file "app::main") with
      | [ { notes = [ (span, _) ]; _ } ] ->
          let noted = String.sub text span.start (span.stop - span.start) in
          if noted <> "count > 0" then Harness.fail "the note is at `%s`" noted
      | actual -> Harness.fail "%s" (String.concat "; " (Support.list_codes actual)));
  Harness.test "the same failure on another path is reported once" (fun () ->
      let actual = list_codes Fixtures.Prover.index_without_a_bound_on_two_paths in
      if actual <> [ "prover.requires" ] then Harness.fail "%s" (String.concat ", " actual))

let () =
  Harness.test "a function parameter of constant time is passed as one that terminates" (fun () ->
      expect_proven Fixtures.Prover.run_of_a_constant_time_task);
  Harness.test "a type's invariant must be well defined" (fun () ->
      expect_not_proven "type Ratio(top: Int64, bottom: Int64)\n  invariant top / bottom > 0\n"
        "prover.division");
  Harness.test "a type's invariant is well defined given the ones before it" (fun () ->
      expect_proven Fixtures.Prover.ratio_invariants);
  Harness.test "a cost clause's bound must be well defined" (fun () ->
      let actual = list_codes Fixtures.Prover.cost_bound_reading_an_element in
      if not (List.mem "prover.requires" actual) then
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
  Harness.test "a slice mutated through a call mutates its run of the list" (fun () ->
      expect_proven ("" ^ Fixtures.Prover.zeroed_slice_of_a_list));
  Harness.test "a slice mutated through a call mutates nothing more than it says" (fun () ->
      expect_not_proven ("" ^ Fixtures.Prover.zeroed_slice_ensured_past_its_run) "prover.ensures");
  Harness.test "an unsigned left shift that fits multiplies by a power of two" (fun () ->
      expect_proven Fixtures.Prover.shift_by_four_of_a_small_byte);
  Harness.test "an unsigned right shift divides by a power of two" (fun () ->
      expect_proven Fixtures.Prover.right_shift_by_two);
  Harness.test "a left shift that may not fit is not known to multiply" (fun () ->
      expect_not_proven Fixtures.Prover.shift_by_four_of_any_byte "prover.ensures");
  Harness.test "a loop that mutates a slice of any elements under a cost clause" (fun () ->
      expect_proven Fixtures.Prover.swap_each);
  Harness.test "a quantifier's body must be well defined" (fun () ->
      expect_not_proven Fixtures.Prover.requires_quantifier_reading_past_the_end "prover.requires");
  Harness.test "a quantifier's body within its range is well defined" (fun () ->
      expect_proven Fixtures.Prover.requires_quantifier_within_the_list);
  Harness.test "a call under a quantifier gives a value for each value, not one for all" (fun () ->
      expect_not_proven Fixtures.Prover.same_under_a_quantifier "prover.ensures");
  Harness.test "alternatives bind each name to the part that matched" (fun () ->
      expect_proven Fixtures.Prover.or_pattern_binding_a_side_value);
  Harness.test "a match mut binding of alternatives is the part of the alternative that matched"
    (fun () -> expect_proven Fixtures.Prover.match_mut_on_sides);
  Harness.test "a slice chosen by a condition gives its run back to the collection it views"
    (fun () -> expect_proven Fixtures.Prover.slice_chosen_by_a_flag);
  Harness.test "a copy of a mut slice parameter cannot be passed mut" (fun () ->
      expect_not_proven Fixtures.Prover.copy_of_a_mut_slice_passed_mut "prover.unsupported");
  Harness.test "a slice that a loop assigns cannot be passed mut after the loop" (fun () ->
      expect_not_proven Fixtures.Prover.slice_assigned_in_a_loop_then_passed_mut
        "prover.unsupported");
  Harness.test "a slice chosen by a condition may mutate either collection" (fun () ->
      expect_not_proven Fixtures.Prover.slice_chosen_by_a_flag_ensured_to_keep_the_second
        "prover.ensures");
  Harness.test "a match mut binding of alternatives is no other alternative's part" (fun () ->
      expect_not_proven Fixtures.Prover.match_mut_on_sides_with_a_wrong_ensures "prover.ensures");
  Harness.test "a mut lend in a condition is written back on each path" (fun () ->
      expect_proven Fixtures.Prover.if_condition_bumping_an_element);
  Harness.test "a mut lend in a condition is written back where the condition holds" (fun () ->
      expect_not_proven Fixtures.Prover.if_condition_bumping_a_positive_element "prover.ensures");
  Harness.test "a mut lend in a condition is written back where the condition fails" (fun () ->
      expect_not_proven Fixtures.Prover.if_condition_bumping_a_negative_element "prover.ensures");
  Harness.test "a mut lend in a loop's condition is written back" (fun () ->
      expect_proven Fixtures.Prover.while_condition_bumping_an_element);
  Harness.test "a mut lend in the right operand of && is written back where the operand ran"
    (fun () -> expect_proven Fixtures.Prover.and_operand_bumping_an_element_under_a_flag);
  Harness.test "a mut lend in the right operand of && changes the element" (fun () ->
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
  Harness.test "an answer in the cache is read, and the solver is not run" (fun () ->
      let query = make_self_comparison ">=" in
      let request = Solver.make_request query in
      let cache =
        {
          Solver.find =
            (fun key -> if key = Solver.For_testing.hash_query query then Some "proven\n" else None);
          add = (fun _ _ -> Harness.fail "kept an answer the cache already had");
        }
      in
      match Solver.find ~cache () with
      | Error message -> Harness.fail "%s" message
      | Ok solver ->
          if List.hd (Solver.solve_all solver [ (request, query) ]) <> Solver.Proven then
            Harness.fail "expected the cached answer";
          if Solver.count_queries_run solver <> 0 then Harness.fail "ran the solver");
  Harness.test "a proven answer in the cache is read whatever values the request asks for"
    (fun () ->
      let query = make_self_comparison ">=" in
      let request =
        Solver.make_request
          ~symbols:[ Logic.Symbol.Variable { label = "compared"; numbers = [] } ]
          query
      in
      let cache =
        {
          Solver.find =
            (fun key -> if key = Solver.For_testing.hash_query query then Some "proven\n" else None);
          add = (fun _ _ -> Harness.fail "kept an answer the cache already had");
        }
      in
      match Solver.find ~cache () with
      | Error message -> Harness.fail "%s" message
      | Ok solver ->
          if List.hd (Solver.solve_all solver [ (request, query) ]) <> Solver.Proven then
            Harness.fail "expected the cached answer";
          if Solver.count_queries_run solver <> 0 then Harness.fail "ran the solver");
  Harness.test "each solver keeps its own answers" (fun () ->
      let query = make_self_comparison "<" in
      let request = Solver.make_request query in
      match (Solver.find (), Solver.find ()) with
      | Ok first, Ok second ->
          ignore (Solver.solve_all first [ (request, query) ]);
          ignore (Solver.solve_all second [ (request, query) ]);
          if Solver.count_queries_run second <> 1 then
            Harness.fail "the second solver ran %d queries" (Solver.count_queries_run second)
      | Error message, _ | _, Error message -> Harness.fail "%s" message);
  Harness.test "a solved answer is added to the cache under its query's key" (fun () ->
      let query = make_self_comparison "<=" in
      let request = Solver.make_request query in
      let cached_answers = Hashtbl.create 1 in
      let cache =
        { Solver.find = Hashtbl.find_opt cached_answers; add = Hashtbl.replace cached_answers }
      in
      match Solver.find ~cache () with
      | Error message -> Harness.fail "%s" message
      | Ok solver ->
          ignore (Solver.solve_all solver [ (request, query) ]);
          if Solver.count_queries_run solver <> 1 then Harness.fail "did not run the solver";
          if
            Hashtbl.find_opt cached_answers (Solver.For_testing.hash_query query) <> Some "proven\n"
          then Harness.fail "the cache does not have the answer");
  let find_obligation_query text code =
    let packages = Support.setup [ ("app::main", text) ] in
    let key = List.hd (Support.list_declarations packages (Support.parse_module "app::main")) in
    match
      Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
        (Resolve.Names.make_key key)
    with
    | Obligations { obligations; _ } ->
        List.find_map
          (fun (obligation : Prover.State.obligation) ->
            if obligation.code = code then Some obligation.query else None)
          obligations
    | Unsupported _ | Not_proven_here -> None
  in
  Harness.test "an unknown answer without an uninterpreted sort is not searched further" (fun () ->
      match (find_obligation_query Fixtures.Prover.sum_of_two_cubes Ensures, Solver.find ()) with
      | None, _ -> Harness.fail "no obligation of the `ensures`"
      | _, Error message -> Harness.fail "%s" message
      | Some query, Ok solver ->
          let request = Solver.make_request query in
          if List.hd (Solver.solve_all solver [ (request, query) ]) <> Unknown then
            Harness.fail "expected an unknown answer";
          if Solver.count_queries_run solver <> 1 then
            Harness.fail "ran %d queries" (Solver.count_queries_run solver));
  Harness.test "a second request for a query solved in a small model runs one query" (fun () ->
      match
        ( find_obligation_query Fixtures.Prover.addition_under_an_exists_in_a_forall Overflow,
          Solver.find () )
      with
      | None, _ -> Harness.fail "no obligation of the addition"
      | _, Error message -> Harness.fail "%s" message
      | Some query, Ok solver -> (
          let first = Solver.make_request query
          and second = Solver.make_request ~terms:[ (Logic.Symbol.Reached 0, Logic.int 1) ] query in
          match List.hd (Solver.solve_all solver [ (first, query) ]) with
          | Proven | Unknown -> Harness.fail "expected a counterexample"
          | Counterexample _ ->
              let queries_before = Solver.count_queries_run solver in
              ignore (Solver.solve_all solver [ (second, query) ]);
              let queries_run = Solver.count_queries_run solver - queries_before in
              if queries_run <> 1 then Harness.fail "ran %d queries" queries_run));
  Harness.test "a function defined by a quantified formula reaches the solver as a definition"
    (fun () ->
      match find_obligation_query Fixtures.Prover.increment_of_a_word_count Overflow with
      | None -> Harness.fail "no obligation of the addition"
      | Some query ->
          let text = Logic.show_query query in
          if not (String.includes ~affix:"(define-fun " text) then Harness.fail "query %s" text);
  Harness.test "a query's text names nothing by its Truss name" (fun () ->
      let packages = Support.setup [ ("app::main", Fixtures.Prover.addition_that_can_overflow) ] in
      let key = List.hd (Support.list_declarations packages (Support.parse_module "app::main")) in
      match
        Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
          (Resolve.Names.make_key key)
      with
      | Obligations { obligations = [ obligation ]; _ } ->
          let text = Logic.show_query obligation.query in
          if String.includes ~affix:"count" text then Harness.fail "the text names `count`: %s" text
      | _ -> Harness.fail "expected one obligation");
  Harness.test "renaming a function and its parameter gives the same query" (fun () ->
      let key_of text =
        let packages = Support.setup [ ("app::main", text) ] in
        let key = List.hd (Support.list_declarations packages (Support.parse_module "app::main")) in
        match
          Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
            (Resolve.Names.make_key key)
        with
        | Obligations { obligations = [ obligation ]; _ } ->
            Solver.For_testing.hash_query obligation.query
        | _ -> "none"
      in
      let first = key_of Fixtures.Prover.addition_that_can_overflow in
      let second = key_of Fixtures.Prover.addition_of_a_total_that_can_overflow in
      if first <> second || first = "none" then Harness.fail "%s and %s" first second)

let () =
  Harness.test "a slice of a whole array is within it" (fun () ->
      expect_proven Fixtures.Prover.reverse_of_a_whole_array);
  Harness.test "a loop that mutates an array's elements keeps their potentials" (fun () ->
      expect_proven Fixtures.Prover.array_reset);
  Harness.test "a slice of an array is within it only as far as its count" (fun () ->
      expect_not_proven Fixtures.Prover.reverse_of_an_array_after_its_first "prover.requires")

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
              ( "app::main",
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
              Path.equal declaration.path (Support.make_top_path "app::main" "f"))
            (Support.list_declarations packages (Support.parse_module "app::main"))
        in
        match
          Support.read_proofs (Support.make_database packages) (Support.parse_file "app::main")
            (Resolve.Names.make_key key)
        with
        | Obligations { obligations; _ } ->
            List.fold_left
              (fun most (obligation : Prover.State.obligation) ->
                let text = Logic.show_query obligation.query in
                max most (String.find_all ~sub:"12345" (fun _ matches -> matches + 1) text 0))
              0 obligations
        | _ ->
            Harness.fail "expected obligations";
            0
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
      goal = Operation (">", [ Apply (variable "f", [ Symbol (variable "n") ]); int 0 ]);
    }

let () =
  let open Logic in
  let i_term = Symbol (variable "i") and j_term = Symbol (variable "j") in
  let applied_f term = Apply (variable "f", [ term ])
  and applied_g term = Apply (variable "g", [ term ]) in
  let positive term = Operation (">", [ term; int 0 ]) in
  let expect fact fragment =
    let text = render_triggered fact in
    if not (String.includes ~affix:fragment text) then
      Harness.fail "expected %s in %s" fragment text
  in
  Harness.test "a quantified fact triggers on an application of its variable" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int) ],
             Operation (">=", [ i_term; int 0 ]) ==> positive (applied_f i_term) ))
        ":pattern ((x0 b0))");
  Harness.test "a trigger has no arithmetic on a bound variable" (fun () ->
      let text =
        render_triggered
          (forall
             ([ (variable "i", Int) ], positive (applied_f (Operation ("+", [ i_term; int 1 ])))))
      in
      if String.includes ~affix:":pattern" text then Harness.fail "%s" text);
  Harness.test "a trigger that would match its own body's larger term is passed over" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int) ],
             Operation ("<", [ applied_f i_term; applied_f (Operation ("+", [ i_term; int 1 ])) ])
             &&& positive (applied_g i_term) ))
        ":pattern ((x2 b0)))");
  Harness.test "a definition triggers on the term it defines" (fun () ->
      let text =
        render_triggered
          (forall
             ( [ (variable "i", Int) ],
               equal (applied_f i_term) (Operation ("+", [ applied_g i_term; int 1 ])) ))
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
      goal = Operation (">", [ Apply (variable "f", [ Symbol (variable "n") ]); int 0 ]);
    }
  in
  Harness.test "a quantified fact with no trigger is told apart" (fun () ->
      if
        not
          (has_untriggered_fact
             (make_query
                (forall
                   ( [ (variable "i", Int) ],
                     positive (applied_f (Operation ("+", [ i_term; int 1 ]))) ))))
      then Harness.fail "a fact on f(i + 1) alone has no trigger";
      if
        has_untriggered_fact
          (make_query (forall ([ (variable "i", Int) ], positive (applied_f i_term))))
      then Harness.fail "a fact on f(i) has one");
  Harness.test "variables named by no one application share a trigger" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int); (variable "j", Int) ],
             Operation ("<", [ applied_f i_term; applied_g j_term ]) ))
        ":pattern ((x0 b0) (x2 b1))");
  let count_patterns text = String.find_all ~sub:":pattern" (fun _ matches -> matches + 1) text 0 in
  Harness.test
    "transitivity triggers on all three of its applications, so it makes no matching loop"
    (fun () ->
      let k_term = Symbol (variable "k") in
      let at_most first second =
        Operation ("<=", [ Apply (variable "h", [ first; second ]); int 0 ])
      in
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
      expect_proven Fixtures.Prover.finite_measure_compared_with_itself);
  Harness.test "a function value that uses a capability may give different results" (fun () ->
      expect_not_proven Fixtures.Prover.clock_reading_compared_with_itself "prover.ensures");
  Harness.test "a function value without a time clause is a fresh result" (fun () ->
      expect_not_proven Fixtures.Prover.measure_compared_with_itself "prover.ensures");
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

let check_in_standard text =
  check_file
    (Database.create
       (Support.setup
          [
            ("standard::core", Fixtures.Prover.index_trait);
            ("standard::specification", Fixtures.Prover.sequence_with_index);
            ("standard::probe", text);
          ]))
    (Support.parse_file "standard::probe")

let expect_proven_in_standard text =
  match check_in_standard text with
  | [] -> ()
  | actual ->
      Harness.fail "%s"
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual))

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
      match Support.list_codes (check_in_standard Fixtures.Prover.count_ones_ensured_zero) with
      | [ "prover.ensures" ] -> ()
      | codes -> Harness.fail "expected prover.ensures, found %s" (String.concat ", " codes))

let () =
  Harness.test "an intrinsic operation has its operator's facts" (fun () ->
      expect_proven_in_standard Fixtures.Prover.intrinsic_mask);
  Harness.test "an intrinsic shift has its operator's obligation on the amount" (fun () ->
      match Support.list_codes (check_in_standard Fixtures.Prover.intrinsic_shift_left) with
      | [ "prover.shift" ] -> ()
      | codes -> Harness.fail "expected prover.shift, found %s" (String.concat ", " codes));
  Harness.test "a character made from an integer must be a Unicode scalar value" (fun () ->
      match
        Support.list_codes (check_in_standard Fixtures.Prover.character_converted_from_a_code)
      with
      | [ "prover.requires" ] -> ()
      | codes -> Harness.fail "expected prover.requires, found %s" (String.concat ", " codes))

let () =
  let expect_only_requires text =
    match Support.list_codes (check_in_standard text) with
    | [ "prover.requires" ] -> ()
    | codes -> Harness.fail "expected prover.requires, found %s" (String.concat ", " codes)
  in
  Harness.test "an element of a storage is read only at an index within it" (fun () ->
      expect_only_requires Fixtures.Prover.storage_read_at_an_unchecked_index);
  Harness.test "an element of a storage at an index below its length proves" (fun () ->
      expect_proven_in_standard Fixtures.Prover.storage_read_at_a_checked_index);
  Harness.test "a storage is popped only when it holds an element" (fun () ->
      expect_only_requires Fixtures.Prover.storage_popped_without_a_length);
  Harness.test "a view is sliced only within its length" (fun () ->
      expect_only_requires Fixtures.Prover.view_sliced_past_its_end)

let () =
  let apply = Fixtures.Prover.apply_bounded_by_the_time_of_change in
  Harness.test "a bound that names the time of a callback takes the time of the function passed"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_passing_the_time_of_quick_through));
  Harness.test "a function without a time clause passes a function without one" (fun () ->
      expect_proven (apply ^ Fixtures.Prover.apply_of_slow_without_a_time_clause));
  Harness.test
    "a call that uses nothing is in the logic, whatever its callee's capability parameter"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_in_an_ensures));
  Harness.test "a function without a time clause passes a lambda with a loop without a measure"
    (fun () -> expect_proven (apply ^ Fixtures.Prover.apply_of_a_lambda_looping_without_a_measure));
  Harness.test "an operator on a bound type terminates" (fun () ->
      expect_proven Fixtures.Prover.sum_of_a_bound_type_under_a_time_clause)

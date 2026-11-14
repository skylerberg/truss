(* The prover, against the pinned solver. Each test gives a few small
   definitions and states which obligation is proven or is not. *)

open Harness

let solver = Lazy.force Support.solver

let check database module_ =
  match Checks.diagnostics database module_ with
  | [] -> Prover.diagnostics ~record:(Support.record database) database solver module_
  | errors -> errors

let proven text = Support.no_diagnostics ~check [ ("app::main", text) ]
let not_proven text code = Support.one_diagnostic ~check text code

let codes text =
  let database = Support.setup [ ("app::main", text) ] in
  Support.codes (check database (Support.file_of "app::main"))

(* A file with diagnostics, all of one code, as a cycle of the call graph
   gives at each call in it. *)
let only_code text code =
  match codes text with
  | [] -> fail "no diagnostics"
  | actual ->
      if List.exists (fun other -> other <> code) actual then fail "%s" (String.concat ", " actual)

(* The message of a file's one diagnostic. *)
let message text =
  let database = Support.setup [ ("app::main", text) ] in
  match check database (Support.file_of "app::main") with
  | [ diagnostic ] -> diagnostic.message
  | actual ->
      Printf.sprintf "%d diagnostics: %s" (List.length actual)
        (String.concat "; " (Support.codes actual))

let contains = Substring.contains

(* Operations that could fail *)

let () =
  test "an addition that can overflow" (fun () ->
      not_proven Fixtures.Prover.addition_that_can_overflow "prover.overflow");
  test "an overflow's counterexample names the value" (fun () ->
      let actual = message Fixtures.Prover.overflows_counterexample_names_the_value in
      if not (contains actual "`count` is 255") then fail "message %S" actual);
  test "code generic over an integer trait is proven for each type that implements it" (fun () ->
      proven Fixtures.Prover.code_generic_over_an_integer_trait_is_proven_for;
      let actual = message Fixtures.Prover.code_generic_over_an_integer_trait_is_proven_for_2 in
      if not (contains actual "`Number` is `UInt8`") then fail "message %S" actual);
  test "a requires rules out the overflow" (fun () ->
      proven Fixtures.Prover.requires_rules_out_the_overflow);
  test "a requires clause read from its code holds or fails at a call as the clause written does"
    (fun () ->
      (* The clause can run, so the prover reads its MIR: a short circuit on each side, a field
         read, and a pattern that binds a name the clause then reads. *)
      proven Fixtures.Prover.requires_clause_read_from_its_code_holds_at_a_call;
      not_proven Fixtures.Prover.requires_clause_read_from_its_code_holds_at_a_call_2
        "prover.requires");
  test "a check in an if rules out the overflow" (fun () ->
      proven Fixtures.Prover.check_in_an_if_rules_out_the_overflow);
  test "a division by a value that may be zero" (fun () ->
      not_proven Fixtures.Prover.division_by_a_value_that_may_be_zero "prover.division");
  test "a signed division by -1 can overflow" (fun () ->
      not_proven Fixtures.Prover.signed_division_by_1_can_overflow "prover.overflow");
  test "a shift amount must be less than the width" (fun () ->
      not_proven Fixtures.Prover.shift_amount_must_be_less_than_the_width "prover.shift");
  test "negating the least signed value overflows" (fun () ->
      not_proven Fixtures.Prover.negating_the_least_signed_value_overflows "prover.overflow");
  test "an unreachable that can be reached" (fun () ->
      not_proven Fixtures.Prover.unreachable_that_can_be_reached "prover.unreachable");
  test "an unreachable after a check" (fun () -> proven Fixtures.Prover.unreachable_after_a_check)

(* Contracts *)

let () =
  test "a call must meet its callee's requires" (fun () ->
      not_proven Fixtures.Prover.call_must_meet_its_callees_requires "prover.requires");
  test "a call that meets its callee's requires" (fun () ->
      proven Fixtures.Prover.call_that_meets_its_callees_requires);
  test "an ensures is shown" (fun () -> proven Fixtures.Prover.ensures_is_shown);
  test "an ensures that does not hold" (fun () ->
      not_proven Fixtures.Prover.ensures_that_does_not_hold "prover.ensures");
  test "an ensures holds at an early return" (fun () ->
      not_proven Fixtures.Prover.ensures_holds_at_an_early_return "prover.ensures");
  test "a callee's ensures is a fact after the call" (fun () ->
      proven Fixtures.Prover.callees_ensures_is_a_fact_after_the_call);
  test "a mut argument changes only through the callee's ensures" (fun () ->
      not_proven Fixtures.Prover.mut_argument_changes_only_through_the_callees "prover.ensures")

(* Loops and recursion *)

let () =
  test "a loop with an invariant" (fun () -> proven Fixtures.Prover.loop_with_an_invariant);
  test "a loop invariant that an iteration breaks" (fun () ->
      not_proven Fixtures.Prover.loop_invariant_that_an_iteration_breaks "prover.invariant");
  test "a loop in a function with a time clause must end" (fun () ->
      not_proven Fixtures.Prover.loop_in_a_function_with_a_time_clause_must_end "prover.termination");
  test "a loop that counts up to its bound ends" (fun () ->
      proven Fixtures.Prover.loop_that_counts_up_to_its_bound_ends);
  test "a for loop over a range knows its index is in range" (fun () ->
      proven Fixtures.Prover.for_loop_over_a_range_knows_its_index_is_in_range);
  test "recursion that decreases" (fun () -> proven Fixtures.Prover.recursion_that_decreases);
  test "recursion that does not decrease" (fun () ->
      not_proven Fixtures.Prover.recursion_that_does_not_decrease "prover.termination")

let () =
  test "mutual recursion without measures cannot be shown to end" (fun () ->
      let database =
        Support.setup
          [ ("app::main", Fixtures.Prover.mutual_recursion_without_measures_cannot_be_shown) ]
      in
      match Support.codes (check database (Support.file_of "app::main")) with
      | [ "prover.termination"; "prover.termination" ] -> ()
      | codes -> fail "codes %s" (String.concat ", " codes));
  test "mutual recursion that decreases" (fun () ->
      proven Fixtures.Prover.mutual_recursion_that_decreases);
  test "a function with a time clause cannot call one without" (fun () ->
      not_proven Fixtures.Prover.function_with_a_time_clause_cannot_call_one "prover.termination");
  test "an impl that reaches itself through a generic function cannot be shown to end" (fun () ->
      only_code Fixtures.Prover.impl_that_reaches_itself_through_a_generic "prover.termination")

let tree = Fixtures.Prover.tree

let () =
  test "recursion on a part of a parameter ends" (fun () ->
      proven (tree ^ Fixtures.Prover.recursion_on_a_part_of_a_parameter_ends));
  test "recursion on the parameter itself does not end" (fun () ->
      not_proven
        (tree ^ Fixtures.Prover.recursion_on_the_parameter_itself_does_not_end)
        "prover.termination");
  test "a match with guards ends in an unreachable that is proven" (fun () ->
      proven Fixtures.Prover.match_with_guards_ends_in_an_unreachable_that_is;
      not_proven Fixtures.Prover.match_with_guards_ends_in_an_unreachable_that_is_2
        "prover.unreachable")

(* Proofs *)

let () =
  test "a theorem the solver proves alone" (fun () ->
      proven Fixtures.Prover.theorem_the_solver_proves_alone);
  test "a quantifier over a range" (fun () ->
      not_proven Fixtures.Prover.quantifier_over_a_range "prover.ensures");
  test "an assert in a test is a fact, not an obligation" (fun () ->
      proven Fixtures.Prover.assert_in_a_test_is_a_fact_not_an_obligation);
  test "an assert in a theorem is an obligation" (fun () ->
      not_proven Fixtures.Prover.assert_in_a_theorem_is_an_obligation "prover.assertion")

(* Data *)

let shape = Fixtures.Prover.shape
let point = "type Point(x: Int64, y: Int64)\n  derives Equal\n\n"

let () =
  test "match binds a variant's fields" (fun () ->
      proven (shape ^ Fixtures.Prover.match_binds_a_variants_fields));
  test "a variant's field is in its type's range, and no further" (fun () ->
      not_proven
        (shape ^ Fixtures.Prover.variants_field_is_in_its_types_range_and_no)
        "prover.overflow");
  test "a counterexample shows a variant by its name" (fun () ->
      let actual = message (shape ^ Fixtures.Prover.counterexample_shows_a_variant_by_its_name) in
      if not (contains actual "`shape` is Circle(radius: 9223372036854775807)") then
        fail "message %S" actual);
  test "a requires can match on a parameter" (fun () ->
      proven (shape ^ Fixtures.Prover.requires_can_match_on_a_parameter));
  test "with replaces one field and keeps the others" (fun () ->
      proven (point ^ Fixtures.Prover.with_replaces_one_field_and_keeps_the_others));
  test "derived equality is the solver's equality" (fun () ->
      proven (point ^ Fixtures.Prover.derived_equality_is_the_solvers_equality));
  test "is binds the parts it matches, where it is true" (fun () ->
      proven Fixtures.Prover.is_binds_the_parts_it_matches_where_it_is_true);
  test "? continues with the value inside" (fun () ->
      not_proven Fixtures.Prover.continues_with_the_value_inside "prover.overflow");
  test "? returns an error unchanged" (fun () -> proven Fixtures.Prover.returns_an_error_unchanged)

(* Collections, definitions, and impls *)

let () =
  test "an index must be in bounds" (fun () ->
      not_proven Fixtures.Prover.index_must_be_in_bounds "prover.requires");
  test "an index the requires bounds" (fun () -> proven Fixtures.Prover.index_the_requires_bounds);
  test "an index a range loop bounds" (fun () -> proven Fixtures.Prover.index_a_range_loop_bounds);
  test "assigning to an element checks its index" (fun () ->
      not_proven Fixtures.Prover.assigning_to_an_element_checks_its_index "prover.requires");
  test "a function's ensures is what its callers know" (fun () ->
      proven Fixtures.Prover.functional_body_is_its_functions_definition);
  test "a body with a loop is not a definition" (fun () ->
      not_proven Fixtures.Prover.body_with_a_loop_is_not_a_definition "prover.ensures");
  test "a function without a time clause is not a definition" (fun () ->
      not_proven Fixtures.Prover.function_without_a_time_clause_is_not_a_definition "prover.ensures");
  test "an impl method's contract is read at a call" (fun () ->
      proven Fixtures.Prover.impl_methods_contract_is_read_at_a_call);
  test "a mut argument that is a field leaves the rest of its value as it was" (fun () ->
      proven Fixtures.Prover.mut_argument_that_is_a_field_leaves_the_rest_of);
  test "a mut argument that is a field is known only by the callee's postcondition" (fun () ->
      not_proven Fixtures.Prover.mut_argument_that_is_a_field_is_known_only_by_the "prover.ensures");
  test "assigning a field keeps the other fields" (fun () ->
      proven Fixtures.Prover.assigning_a_field_keeps_the_other_fields)

let measured = Fixtures.Prover.measured

let () =
  test "an impl's method must keep its trait's ensures" (fun () ->
      not_proven
        (measured ^ Fixtures.Prover.impls_method_must_keep_its_traits_ensures)
        "prover.ensures");
  test "an impl's method that keeps its trait's ensures" (fun () ->
      proven (measured ^ Fixtures.Prover.impls_method_that_keeps_its_traits_ensures));
  test "an impl's requires may not be stronger than its trait's" (fun () ->
      not_proven
        (measured ^ Fixtures.Prover.impls_requires_may_not_be_stronger_than_its_traits)
        "prover.requires")

(* Lambdas and callbacks *)

let each_index = Fixtures.Prover.each_index

let () =
  test "a lambda's body is proven where it is written" (fun () ->
      not_proven Fixtures.Prover.lambdas_body_is_proven_where_it_is_written "prover.overflow");
  test "a lambda may rely on its callee's promise about its arguments" (fun () ->
      proven (each_index ^ Fixtures.Prover.lambda_may_rely_on_its_callees_promise_about_its));
  test "a lambda without such a promise knows nothing of its arguments" (fun () ->
      not_proven Fixtures.Prover.lambda_without_such_a_promise_knows_nothing_of_its
        "prover.requires");
  test "a function must keep its promise to its callback" (fun () ->
      not_proven Fixtures.Prover.function_must_keep_its_promise_to_its_callback "prover.requires");
  test "a function that keeps its promise to its callback" (fun () ->
      proven Fixtures.Prover.function_that_keeps_its_promise_to_its_callback)

(* Models *)

let () =
  test "a push's contract, through the list's model" (fun () ->
      proven Fixtures.Prover.pushs_contract_through_the_lists_model);
  test "a push does not keep the length" (fun () ->
      not_proven Fixtures.Prover.push_does_not_keep_the_length "prover.ensures");
  test "an index into a list after a push is in bounds" (fun () ->
      proven Fixtures.Prover.index_into_a_list_after_a_push_is_in_bounds);
  test "identical is the same value, for any type" (fun () ->
      proven Fixtures.Prover.identical_is_the_same_value_for_any_type)

let () =
  test "a loop over a list runs once per element" (fun () ->
      proven Fixtures.Prover.loop_over_a_list_runs_once_per_element);
  test "a loop's element is the list's element at its position" (fun () ->
      proven Fixtures.Prover.loops_element_is_the_lists_element_at_its_position);
  test "a loop over a list does not run once more" (fun () ->
      not_proven Fixtures.Prover.loop_over_a_list_does_not_run_once_more "prover.ensures")

let couple = Fixtures.Prover.couple

let () =
  test "a lending method keeps its contract on each path that lends" (fun () -> proven couple);
  let tagged ensures =
    Fixtures.Prover.ensures ^ ensures ^ "{\n  Tagged(tag: 0, value: mut self.second)\n}\n"
  in
  test "a constructor lent `mut` does not change a field of `self` that it does not lend" (fun () ->
      proven (tagged "  ensures self.first == old(self.first)\n"));
  test "a caller's change to a constructor lent `mut` is written to the lent field" (fun () ->
      not_proven (tagged "  ensures self.second == old(self.second)\n") "prover.ensures");
  test "a caller of a method that lends a constructor `mut` can rely on its `ensures`" (fun () ->
      proven
        (tagged "  ensures self.first == old(self.first)\n"
        ^ Fixtures.Prover.caller_of_a_method_that_lends_a_constructor_mut));
  test "a lending method that lends a part it does not promise" (fun () ->
      not_proven Fixtures.Prover.lending_method_that_lends_a_part_it_does_not_promise
        "prover.ensures");
  test "a loop over a user's collection gets the facts of its `count` and its `element`" (fun () ->
      proven (couple ^ Fixtures.Prover.loop_over_a_users_collection_gets_the_facts_of_its));
  test "the elements that a loop has read meet the postcondition of the collection's `element`"
    (fun () -> proven (couple ^ Fixtures.Prover.elements_that_a_loop_has_read_meet_the));
  test "the elements that a loop has read are not known beyond that postcondition" (fun () ->
      not_proven
        (couple ^ Fixtures.Prover.elements_that_a_loop_has_read_are_not_known_beyond)
        "prover.invariant");
  test "a loop over a range has its indexes as yielded" (fun () ->
      proven Fixtures.Prover.loop_over_a_range_has_its_indexes_as_yielded);
  test "a range loop's index in its clauses is the next index" (fun () ->
      proven Fixtures.Prover.range_loops_index_in_its_clauses_is_the_next_index);
  test "a range loop's index counts from the range's start" (fun () ->
      proven Fixtures.Prover.range_loops_index_counts_from_the_ranges_start);
  test "a range loop's index in its clauses is past the last index at the end" (fun () ->
      not_proven Fixtures.Prover.range_loops_index_in_its_clauses_is_past_the_last
        "prover.invariant");
  test "an inclusive range loop's index in its clauses runs through one past its end" (fun () ->
      proven Fixtures.Prover.inclusive_range_loops_index_in_its_clauses_runs);
  test "a range loop's index bounds its cost" (fun () ->
      proven Fixtures.Prover.range_loops_index_bounds_its_cost);
  test "a loop over a type's own cursor calls its next" (fun () ->
      proven Fixtures.Prover.loop_over_a_types_own_cursor_calls_its_next);
  test "a loop over a cursor in a field calls its next" (fun () ->
      proven Fixtures.Prover.loop_over_a_cursor_in_a_field_calls_its_next);
  (* The loop holds the potential of [output], which the body's amortized
     callee spends and saves, and not the cursor's, which its [next] leaves
     alone. *)
  test "a loop over a cursor counts a body that calls an amortized callee" (fun () ->
      proven Fixtures.Prover.loop_over_a_cursor_counts_a_body_that_calls_an);
  test "a later arm sees an earlier arm's guard's changes" (fun () ->
      proven Fixtures.Prover.later_arm_sees_an_earlier_arms_guards_changes);
  test "assigning an element changes only that element" (fun () ->
      proven Fixtures.Prover.assigning_an_element_changes_only_that_element);
  test "a compound assignment to an element" (fun () ->
      proven Fixtures.Prover.compound_assignment_to_an_element);
  let digit = Fixtures.Prover.digit in
  test "an assignment evaluates its value, then its target's index keys" (fun () ->
      proven (digit ^ Fixtures.Prover.assignment_evaluates_its_value_then_its_targets);
      not_proven
        (digit ^ Fixtures.Prover.assignment_evaluates_its_value_then_its_targets_2)
        "prover.ensures");
  test "a compound assignment evaluates its operand, then its target's index keys, once" (fun () ->
      proven (digit ^ Fixtures.Prover.compound_assignment_evaluates_its_operand_then_its);
      not_proven
        (digit ^ Fixtures.Prover.compound_assignment_evaluates_its_operand_then_its_2)
        "prover.ensures")

(* Laws *)

let monoid = Fixtures.Prover.monoid

let flag_impl empty =
  Printf.sprintf
    "impl Monoid for Flag {\n\
    \  fn empty() -> Flag\n\
    \    cost time finite\n\
    \  {\n\
    \    Flag(on: %s)\n\
    \  }\n\n\
    \  fn combine(self, other: Flag) -> Flag\n\
    \    cost time finite\n\
    \  {\n\
    \    Flag(on: self.on || other.on)\n\
    \  }\n\
     }\n"
    empty

let () =
  test "an impl's methods keep its trait's law" (fun () -> proven (monoid ^ flag_impl "false"));
  test "an impl whose methods break its trait's law" (fun () ->
      not_proven (monoid ^ flag_impl "true") "prover.law");
  test "generic code relies on a bound's laws" (fun () ->
      proven (monoid ^ flag_impl "false" ^ Fixtures.Prover.generic_code_relies_on_a_bounds_laws))

let () =
  test "an impl's method keeps its trait's time clause, so its body is its definition" (fun () ->
      proven (monoid ^ Fixtures.Prover.impls_method_keeps_its_traits_time_clause_so_its))

(* The standard library's integer methods, by the intrinsic operations
   they call *)

let () =
  test "wrapping arithmetic is a remainder" (fun () ->
      proven Fixtures.Prover.wrapping_arithmetic_is_a_remainder);
  test "wrapping subtraction wraps below zero" (fun () ->
      proven Fixtures.Prover.wrapping_subtraction_wraps_below_zero);
  test "saturating addition stops at the bound" (fun () ->
      proven Fixtures.Prover.saturating_addition_stops_at_the_bound);
  test "saturating addition is exact where it fits" (fun () ->
      proven Fixtures.Prover.saturating_addition_is_exact_where_it_fits);
  test "a checked addition is none exactly when it overflows" (fun () ->
      proven Fixtures.Prover.checked_addition_is_none_exactly_when_it_overflows);
  test "a conversion succeeds exactly when the value fits" (fun () ->
      proven Fixtures.Prover.conversion_succeeds_exactly_when_the_value_fits);
  test "a widening conversion keeps the value" (fun () ->
      proven Fixtures.Prover.widening_conversion_keeps_the_value);
  test "a widening conversion costs constant time" (fun () ->
      proven Fixtures.Prover.widening_conversion_costs_constant_time);
  test "a widening conversion keeps a range from a type's invariant" (fun () ->
      proven Fixtures.Prover.widening_keeps_a_range_from_an_invariant);
  test "unwrap_or gives the held value or the default" (fun () ->
      proven Fixtures.Prover.unwrap_or_gives_the_held_value_or_the_default);
  test "wrapping is not exact arithmetic" (fun () ->
      not_proven Fixtures.Prover.wrapping_is_not_exact_arithmetic "prover.ensures")

let doubling = Fixtures.Prover.doubling

let amount_impl replacement =
  Printf.sprintf
    "impl Doubling for Amount {\n\
    \  fn value(self) -> Int64\n\
    \    cost time finite\n\
    \  {\n\
    \    self.cents\n\
    \  }\n\n\
    \  fn doubled(self) -> Bool\n\
    \    cost time finite\n\
    \  {\n\
    \    %s\n\
    \  }\n\
     }\n"
    replacement

let () =
  test "a replacement that gives the provided body's result" (fun () ->
      proven (doubling ^ amount_impl "self.cents > 0"));
  test "a replacement that gives another result" (fun () ->
      not_proven (doubling ^ amount_impl "self.cents >= 0") "prover.ensures")

(* Type invariants *)

let span = "type Span(low: Int64, high: Int64)\n  invariant low <= high\n\n"

let () =
  test "building a value must meet its invariant" (fun () ->
      not_proven
        (span ^ Fixtures.Prover.building_a_value_must_meet_its_invariant)
        "prover.invariant");
  test "building a value that meets its invariant" (fun () ->
      proven (span ^ Fixtures.Prover.building_a_value_that_meets_its_invariant));
  test "a parameter meets its invariant" (fun () ->
      proven (span ^ Fixtures.Prover.parameter_meets_its_invariant));
  test "a mut parameter must meet its invariant when the function returns" (fun () ->
      not_proven
        (span ^ Fixtures.Prover.mut_parameter_must_meet_its_invariant_when_the)
        "prover.invariant");
  test "a body may break an invariant between calls" (fun () ->
      proven (span ^ Fixtures.Prover.body_may_break_an_invariant_between_calls));
  test "a value passed to a call must meet its invariant" (fun () ->
      not_proven
        (span ^ Fixtures.Prover.value_passed_to_a_call_must_meet_its_invariant)
        "prover.invariant");
  test "a private method that takes mut self is a step of an update" (fun () ->
      proven (span ^ Fixtures.Prover.private_method_that_takes_mut_self_is_a_step_of_an))

(* Functions named as values *)

let run = Fixtures.Prover.run

let () =
  test "a named function that keeps its parameter type's cost" (fun () ->
      proven (run ^ Fixtures.Prover.named_function_that_keeps_its_parameter_types_cost));
  test "a named function that does not keep its parameter type's cost" (fun () ->
      not_proven
        (run ^ Fixtures.Prover.named_function_that_does_not_keep_its_parameter)
        "prover.cost");
  test "a named function must accept every argument its parameter's type promises" (fun () ->
      not_proven Fixtures.Prover.named_function_must_accept_every_argument_its "prover.requires");
  test "a named function that accepts every argument its parameter's type promises" (fun () ->
      proven Fixtures.Prover.named_function_that_accepts_every_argument_its);
  test "naming a function that reaches back is recursion that cannot be shown to end" (fun () ->
      not_proven
        (run ^ Fixtures.Prover.naming_a_function_that_reaches_back_is_recursion)
        "prover.termination")

(* Sequences *)

let () =
  test "a list literal has its elements in order" (fun () ->
      proven Fixtures.Prover.list_literal_has_its_elements_in_order);
  test "a list literal has its length" (fun () ->
      proven Fixtures.Prover.list_literal_has_its_length);
  test "an array literal has its elements" (fun () ->
      proven Fixtures.Prover.array_literal_has_its_elements);
  test "an index below an array's count is within it" (fun () ->
      proven Fixtures.Prover.index_below_an_arrays_count_is_within_it);
  test "an index at an array's count is not" (fun () ->
      not_proven Fixtures.Prover.index_at_an_arrays_count_is_not "prover.requires");
  test "a non-empty list literal is one allocation" (fun () ->
      proven Fixtures.Prover.non_empty_list_literal_is_one_allocation);
  test "sequences with the same elements are identical" (fun () ->
      proven Fixtures.Prover.sequences_with_the_same_elements_are_identical);
  test "sequences that differ in one element are not identical" (fun () ->
      not_proven Fixtures.Prover.sequences_that_differ_in_one_element_are_not "prover.ensures")

(* Bitwise operations *)

let () =
  test "a value or itself is itself, bit for bit" (fun () ->
      proven Fixtures.Prover.value_or_itself_is_itself_bit_for_bit);
  test "a value xor itself is zero" (fun () -> proven Fixtures.Prover.value_xor_itself_is_zero);
  test "signed bitwise operations are two's complement" (fun () ->
      proven Fixtures.Prover.signed_bitwise_operations_are_twos_complement);
  test "a shift by a literal is a multiplication" (fun () ->
      proven Fixtures.Prover.shift_by_a_literal_is_a_multiplication);
  test "a bit-vector assertion holds for every value of its variables" (fun () ->
      not_proven Fixtures.Prover.bit_vector_assertion_holds_for_every_value "prover.assertion");
  test "a bit-vector assertion states its hypotheses" (fun () ->
      proven Fixtures.Prover.bit_vector_assertion_states_its_hypotheses);
  test "a bitwise fact that does not hold has a counterexample" (fun () ->
      not_proven Fixtures.Prover.bitwise_fact_that_does_not_hold_has_a "prover.ensures")

(* Slices *)

let () =
  test "a slice's elements are its collection's, from its start" (fun () ->
      proven Fixtures.Prover.slices_elements_are_its_collections_from_its_start);
  test "a list passed as a slice is a view with its model" (fun () ->
      proven Fixtures.Prover.list_passed_as_a_slice_is_a_view_with_its_model);
  test "a slice must be within its collection" (fun () ->
      not_proven Fixtures.Prover.slice_must_be_within_its_collection "prover.requires");
  test "two slices lent together must not overlap" (fun () ->
      not_proven Fixtures.Prover.two_slices_lent_together_must_not_overlap "prover.disjoint");
  test "two halves of a list can be lent together" (fun () ->
      proven Fixtures.Prover.two_halves_of_a_list_can_be_lent_together)

(* Strings *)

let () =
  test "a string literal's length is its bytes'" (fun () ->
      proven Fixtures.Prover.string_literals_length_is_its_bytes);
  test "pushing text onto a string adds its length" (fun () ->
      proven Fixtures.Prover.pushing_text_onto_a_string_adds_its_length);
  test "a string pattern matches text with its bytes" (fun () ->
      proven Fixtures.Prover.string_pattern_matches_text_with_its_bytes);
  test "an interpolated string is a string about which little is known" (fun () ->
      not_proven Fixtures.Prover.interpolated_string_is_a_string_about_which_little "prover.ensures")

(* Tagged templates *)

let shout = Fixtures.Prover.shout

let () =
  test "a tagged template meets its tag's requires" (fun () ->
      proven (shout ^ Fixtures.Prover.tagged_template_meets_its_tags_requires));
  test "a call of from_template through a bound cannot see the tag's requires" (fun () ->
      not_proven Fixtures.Prover.call_of_from_template_through_a_bound_cannot_see "prover.requires");
  test "a tagged template that does not meet its tag's requires" (fun () ->
      not_proven
        (shout ^ Fixtures.Prover.tagged_template_that_does_not_meet_its_tags)
        "prover.requires")

(* Floats *)

let () =
  test "float equality is reflexive, even for NaN" (fun () ->
      proven Fixtures.Prover.float_equality_is_reflexive_even_for_nan);
  test "every float is ordered, NaN last" (fun () ->
      proven Fixtures.Prover.every_float_is_ordered_nan_last);
  test "float arithmetic is exact where IEEE 754 is" (fun () ->
      proven Fixtures.Prover.float_arithmetic_is_exact_where_ieee_754_is);
  test "adding zero keeps a float equal, with -0.0 equal to 0.0" (fun () ->
      proven Fixtures.Prover.adding_zero_keeps_a_float_equal_with_0_0_equal_to);
  test "adding one does not always make a float larger" (fun () ->
      not_proven Fixtures.Prover.adding_one_does_not_always_make_a_float_larger "prover.ensures");
  test "a derived equality over floats compares field by field" (fun () ->
      proven Fixtures.Prover.derived_equality_over_floats_compares_field_by);
  test "equal points have equal fields" (fun () ->
      proven Fixtures.Prover.equal_points_have_equal_fields);
  test "points equal by their fields are not identical" (fun () ->
      not_proven Fixtures.Prover.points_equal_by_their_fields_are_not_identical "prover.ensures");
  test "a float counterexample is written as Truss writes floats" (fun () ->
      let actual = message Fixtures.Prover.float_counterexample_is_written_as_truss_writes in
      if not (contains actual "infinity" || contains actual "NaN") then fail "message %S" actual)

(* Capabilities *)

let dice = Fixtures.Prover.dice

let () =
  test "a capability's method keeps its ensures" (fun () ->
      proven (dice ^ Fixtures.Prover.capabilitys_method_keeps_its_ensures));
  test "two calls of a capability's method may differ" (fun () ->
      not_proven
        (dice ^ Fixtures.Prover.two_calls_of_a_capabilitys_method_may_differ)
        "prover.ensures");
  test "a call must meet a capability method's requires" (fun () ->
      not_proven Fixtures.Prover.call_must_meet_a_capability_methods_requires "prover.requires")

(* Sets and maps *)

let () =
  test "a set contains its inserted elements" (fun () ->
      proven Fixtures.Prover.set_contains_its_inserted_elements);
  test "inserting an element a set contains leaves it unchanged" (fun () ->
      proven Fixtures.Prover.inserting_an_element_a_set_contains_leaves_it);
  test "inserting into a set may change it" (fun () ->
      not_proven Fixtures.Prover.inserting_into_a_set_may_change_it "prover.ensures");
  test "a map holds an inserted value under its key" (fun () ->
      proven Fixtures.Prover.map_holds_an_inserted_value_under_its_key);
  test "a map keeps its other keys' values" (fun () ->
      proven Fixtures.Prover.map_keeps_its_other_keys_values)

(* Literals of maps and sets, any, provide, and let else *)

let () =
  test "a map literal holds each key's value" (fun () ->
      proven Fixtures.Prover.map_literal_holds_each_keys_value);
  test "a map literal's keys must be distinct" (fun () ->
      not_proven Fixtures.Prover.map_literals_keys_must_be_distinct "prover.requires");
  test "a set literal contains its listed elements and nothing else" (fun () ->
      proven Fixtures.Prover.set_literal_contains_its_listed_elements_and);
  test "any is one allocation" (fun () -> proven Fixtures.Prover.any_is_one_allocation);
  test "a provided implementation's calls keep the capability's contract" (fun () ->
      proven (dice ^ Fixtures.Prover.provided_implementations_calls_keep_the));
  test "an implementation of a capability keeps the capability's contract" (fun () ->
      not_proven (dice ^ Fixtures.Prover.implementation_of_a_capability_keeps_the) "prover.ensures");
  test "a capability's broken contract is named as the capability's" (fun () ->
      let actual = message (dice ^ Fixtures.Prover.capabilitys_broken_contract_is_named_as_the) in
      if not (contains actual "The capability's `result >= 1 && result <= 6`") then
        fail "found: %s" actual);
  test "an implementation of a capability that keeps its contract proves" (fun () ->
      proven (dice ^ Fixtures.Prover.implementation_of_a_capability_that_keeps_its));
  test "let else continues where its pattern matched" (fun () ->
      proven Fixtures.Prover.let_else_continues_where_its_pattern_matched);
  test "a quantifier's pattern takes each element apart" (fun () ->
      proven Fixtures.Prover.quantifiers_pattern_takes_each_element_apart);
  test "a quantifier over a range may ignore its index" (fun () ->
      proven Fixtures.Prover.quantifier_over_a_range_may_ignore_its_index);
  test "a quantifier over a list ranges over its elements" (fun () ->
      proven Fixtures.Prover.quantifier_over_a_list_ranges_over_its_elements)

(* Places lent together *)

let swap = Fixtures.Prover.swap

let () =
  test "two elements lent together must be different elements" (fun () ->
      not_proven
        (swap ^ Fixtures.Prover.two_elements_lent_together_must_be_different)
        "prover.disjoint");
  test "two different elements can be lent together" (fun () ->
      proven (swap ^ Fixtures.Prover.two_different_elements_can_be_lent_together));
  test "parallel branches that change elements must change different ones" (fun () ->
      not_proven Fixtures.Prover.parallel_branches_that_change_elements_must_change
        "prover.disjoint")

(* Where paths join *)

let () =
  test "self changed on one path is joined with the other" (fun () ->
      not_proven Fixtures.Prover.self_changed_on_one_path_is_joined_with_the_other "prover.ensures");
  test "a lending method's `ensures` holds for the part lent on each path" (fun () ->
      not_proven Fixtures.Prover.lending_methods_ensures_holds_for_the_part_lent_on "prover.ensures")

(* Loop changes *)

let () =
  test "a loop forgets a list it changes through a method" (fun () ->
      not_proven Fixtures.Prover.loop_forgets_a_list_it_changes_through_a_method "prover.assertion");
  test "a loop forgets a record whose field it assigns" (fun () ->
      not_proven Fixtures.Prover.loop_forgets_a_record_whose_field_it_assigns "prover.assertion");
  test "a loop forgets self when it changes it" (fun () ->
      not_proven Fixtures.Prover.loop_forgets_self_when_it_changes_it "prover.assertion")

(* Costs *)

let constant_step = Fixtures.Prover.constant_step

let () =
  test "a body with no calls is O(1)" (fun () -> proven Fixtures.Prover.body_with_no_calls_is_o_1);
  test "calls to O(1) functions are O(1)" (fun () ->
      proven (constant_step ^ Fixtures.Prover.calls_to_o_1_functions_are_o_1));
  test "a call to a function with no bound on its time" (fun () ->
      not_proven Fixtures.Prover.call_to_a_function_with_no_bound_on_its_time "prover.cost");
  test "a loop over a range is linear" (fun () ->
      proven (constant_step ^ Fixtures.Prover.loop_over_a_range_is_linear));
  test "a loop over a range is not constant" (fun () ->
      not_proven (constant_step ^ Fixtures.Prover.loop_over_a_range_is_not_constant) "prover.cost");
  test "nested loops over ranges are quadratic" (fun () ->
      proven (constant_step ^ Fixtures.Prover.nested_loops_over_ranges_are_quadratic));
  test "a loop whose iterations cost their index is quadratic" (fun () ->
      proven Fixtures.Prover.loop_whose_iterations_cost_their_index_is);
  test "a loop over a list runs once per element" (fun () ->
      proven (constant_step ^ Fixtures.Prover.loop_over_a_list_runs_once_per_element_2));
  test "an iteration's cost is the larger of its branches'" (fun () ->
      proven Fixtures.Prover.iterations_cost_is_the_larger_of_its_branches);
  test "a while loop runs at most its measure's times" (fun () ->
      proven Fixtures.Prover.while_loop_runs_at_most_its_measures_times);
  test "recursion on one less is linear" (fun () ->
      proven Fixtures.Prover.recursion_on_one_less_is_linear);
  test "recursion on one less is not constant" (fun () ->
      not_proven Fixtures.Prover.recursion_on_one_less_is_not_constant "prover.cost");
  test "recursion on half is logarithmic" (fun () ->
      proven Fixtures.Prover.recursion_on_half_is_logarithmic);
  test "functions that call each other in a cycle share their constants" (fun () ->
      proven Fixtures.Prover.functions_that_call_each_other_in_a_cycle_share);
  test "a quantifier in code runs over its range" (fun () ->
      proven Fixtures.Prover.quantifier_in_code_runs_over_its_range);
  test "calls through a function value are counted exactly" (fun () ->
      proven Fixtures.Prover.calls_through_a_function_value_are_counted_exactly);
  test "calling a function value twice per element is not once" (fun () ->
      not_proven Fixtures.Prover.calling_a_function_value_twice_per_element_is_not "prover.cost");
  test "a caller counts the calls its callee promises" (fun () ->
      proven Fixtures.Prover.caller_counts_the_calls_its_callee_promises);
  test "a loop's cost clause bounds its cost so far" (fun () ->
      proven Fixtures.Prover.loops_cost_clause_bounds_its_cost_so_far);
  test "a function value with an O(1) type is one unit" (fun () ->
      proven Fixtures.Prover.function_value_with_an_o_1_type_is_one_unit);
  test "a lambda must meet its type's cost" (fun () ->
      not_proven Fixtures.Prover.lambda_must_meet_its_types_cost "prover.cost");
  test "nothing allocates without a block to allocate" (fun () ->
      proven Fixtures.Prover.nothing_allocates_without_a_block_to_allocate);
  test "building an indirect variant allocates" (fun () ->
      not_proven Fixtures.Prover.building_an_indirect_variant_allocates "prover.cost");
  test "an indirect variant is one allocation" (fun () ->
      proven Fixtures.Prover.indirect_variant_is_one_allocation);
  test "nested loops are not linear" (fun () ->
      not_proven (constant_step ^ Fixtures.Prover.nested_loops_are_not_linear) "prover.cost");
  test "two recursive calls on one less are not linear" (fun () ->
      not_proven Fixtures.Prover.two_recursive_calls_on_one_less_are_not_linear "prover.cost");
  test "functions in a cycle that branch are not linear" (fun () ->
      not_proven Fixtures.Prover.functions_in_a_cycle_that_branch_are_not_linear "prover.cost");
  test "a callback's time is not free" (fun () ->
      not_proven Fixtures.Prover.callbacks_time_is_not_free "prover.cost");
  test "calls through a lambda that captures the function value are not known" (fun () ->
      not_proven Fixtures.Prover.calls_through_a_lambda_that_captures_the_function "prover.cost");
  test "a quantifier over a costly body is not linear" (fun () ->
      not_proven Fixtures.Prover.quantifier_over_a_costly_body_is_not_linear "prover.cost");
  test "a loop with no measure has no bound" (fun () ->
      let actual = codes Fixtures.Prover.loop_with_no_measure_has_no_bound in
      if not (List.mem "prover.cost" actual && List.mem "prover.termination" actual) then
        fail "%s" (String.concat ", " actual));
  test "a loop's cost clause that is too small" (fun () ->
      not_proven Fixtures.Prover.loops_cost_clause_that_is_too_small "prover.cost");
  test "calls of a capability's method are counted" (fun () ->
      proven Fixtures.Prover.calls_of_a_capabilitys_method_are_counted);
  test "a callee's allocations add up" (fun () -> proven Fixtures.Prover.callees_allocations_add_up);
  test "a lambda's time is bounded where it is written" (fun () ->
      proven Fixtures.Prover.lambdas_time_is_bounded_where_it_is_written);
  test "a lambda that loops over its argument has no bound" (fun () ->
      let actual = codes Fixtures.Prover.lambda_that_loops_over_its_argument_has_no_bound in
      if not (List.mem "prover.cost" actual) then fail "%s" (String.concat ", " actual));
  test "a loop's cost clause over its received parts" (fun () ->
      proven (constant_step ^ Fixtures.Prover.loops_cost_clause_over_its_received_parts));
  test "an impl's method keeps its trait's cost" (fun () ->
      not_proven Fixtures.Prover.impls_method_keeps_its_traits_cost "prover.cost")

(* Amortized costs *)

let meter = Fixtures.Prover.meter

let () =
  test "saving and spending potential are amortized O(1)" (fun () -> proven meter);
  test "spending potential is not O(1) without it" (fun () ->
      not_proven Fixtures.Prover.spending_potential_is_not_o_1_without_it "prover.cost");
  test "a plain bound pays for the potential it is given" (fun () ->
      proven (meter ^ Fixtures.Prover.plain_bound_pays_for_the_potential_it_is_given));
  test "a plain bound that does not pay for the potential it uses" (fun () ->
      not_proven
        (meter ^ Fixtures.Prover.plain_bound_that_does_not_pay_for_the_potential_it)
        "prover.cost");
  test "a loop that spends potential telescopes" (fun () ->
      proven (meter ^ Fixtures.Prover.loop_that_spends_potential_telescopes));
  test "a loop that spends potential it was given is not linear in its count" (fun () ->
      let actual = codes (meter ^ Fixtures.Prover.loop_that_spends_potential_it_was_given_is_not) in
      if actual <> [ "prover.cost" ] then fail "%s" (String.concat ", " actual));
  test "a list's potential is its elements', through its model" (fun () ->
      proven (meter ^ Fixtures.Prover.lists_potential_is_its_elements_through_its_model));
  let encoder = "type Encoder(bytes: List[UInt8])\n\n" in
  test "a record with no potential clause holds its parts'" (fun () ->
      proven (encoder ^ Fixtures.Prover.record_with_no_potential_clause_holds_its_parts));
  test "a loop that pushes into a record's list is amortized linear" (fun () ->
      proven (encoder ^ Fixtures.Prover.loop_that_pushes_into_a_records_list_is_amortized));
  let bag = Fixtures.Prover.bag in
  test "a method that lends a part `mut` is not charged for the caller's changes to it" (fun () ->
      proven bag);
  test "a caller that raises a lent part's potential pays for it" (fun () ->
      let actual =
        codes (meter ^ bag ^ Fixtures.Prover.caller_that_raises_a_lent_parts_potential_pays_for)
      in
      if actual <> [ "prover.cost" ] then fail "%s" (String.concat ", " actual));
  test "a caller that lowers a lent part's potential is paid by it" (fun () ->
      proven (meter ^ bag ^ Fixtures.Prover.caller_that_lowers_a_lent_parts_potential_is_paid));
  test "a potential below zero" (fun () ->
      not_proven "type Debt(owed: Int64)\n  cost potential owed\n" "prover.cost");
  test "a potential its invariant keeps at or above zero" (fun () ->
      proven Fixtures.Prover.potential_its_invariant_keeps_at_or_above_zero)

(* Holes *)

(* The number of holes in a file's proofs. *)
let holes text =
  let database = Support.setup [ ("app::main", text) ] in
  List.fold_left
    (fun total declaration ->
      match Query.demand database Prover.proof (Resolve.Names.key_of declaration) with
      | Obligations outcome -> total + List.length outcome.holes
      | Unsupported _ | Not_proven_here -> total)
    0
    (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))

let () =
  test "a todo in a theorem is a hole, not a failure" (fun () ->
      let text = Fixtures.Prover.todo_in_a_theorem_is_a_hole_not_a_failure in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a todo in a proof block leaves the rest of its path to it" (fun () ->
      let text = Fixtures.Prover.todo_in_a_proof_block_leaves_the_rest_of_its_path in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a contract on a body that is not written waits for it, and is no hole" (fun () ->
      let text = Fixtures.Prover.contract_on_a_body_that_is_not_written_waits_for in
      proven text;
      if holes text <> 0 then fail "%d holes" (holes text));
  test "the code before a todo is still proven" (fun () ->
      not_proven Fixtures.Prover.code_before_a_todo_is_still_proven "prover.requires");
  test "an impl's laws wait while one of its methods is not written" (fun () ->
      proven Fixtures.Prover.impls_laws_wait_while_one_of_its_methods_is_not);
  test "a type that contains itself through a map's values is read" (fun () ->
      proven Fixtures.Prover.type_that_contains_itself_through_a_maps_values_is)

(* Code that does not run *)

let () =
  test "a lambda's result is in range only for arguments in range" (fun () ->
      not_proven Fixtures.Prover.lambdas_result_is_in_range_only_for_arguments_in "prover.ensures");
  test "an uncalled lambda's calls show nothing of the path" (fun () ->
      not_proven Fixtures.Prover.uncalled_lambdas_calls_show_nothing_of_the_path "prover.ensures");
  test "a lambda whose arguments cannot meet its requires shows nothing of the path" (fun () ->
      not_proven Fixtures.Prover.lambda_whose_arguments_cannot_meet_its_requires "prover.ensures");
  test "a quantifier over an empty range shows nothing of the path" (fun () ->
      not_proven Fixtures.Prover.quantifier_over_an_empty_range_shows_nothing_of "prover.ensures");
  test "a lambda over a type no value has shows nothing of the path" (fun () ->
      not_proven Fixtures.Prover.lambda_over_a_type_no_value_has_shows_nothing_of "prover.ensures");
  test "a todo in a law's proof is a hole that stands for the law" (fun () ->
      let text =
        monoid ^ flag_impl "true" ^ "\nproof Monoid.left_identity for Flag {\n  todo\n}\n"
      in
      proven text;
      if holes text <> 1 then fail "%d holes" (holes text))

(* A caller assumes only proven facts *)

let () =
  test "a trait's ensures holds of an impl's method only where the trait's requires does" (fun () ->
      not_proven Fixtures.Prover.traits_ensures_holds_of_an_impls_method_only_where "prover.ensures");
  test "a law of an unfinished impl is a hole where it is assumed" (fun () ->
      let text = Fixtures.Prover.law_of_an_unfinished_impl_is_a_hole_where_it_is in
      if holes text <> 1 then fail "%d holes" (holes text));
  test "a law whose proof holds a todo is a hole where it is assumed" (fun () ->
      let text = Fixtures.Prover.law_whose_proof_holds_a_todo_is_a_hole_where_it_is in
      if holes text <> 2 then fail "%d holes" (holes text));
  test "each impl of a trait with arguments keeps its own laws" (fun () ->
      not_proven Fixtures.Prover.each_impl_of_a_trait_with_arguments_keeps_its_own "prover.law");
  test "an element changed through a lend meets its invariant when the lend ends" (fun () ->
      not_proven Fixtures.Prover.element_changed_through_a_lend_meets_its_invariant
        "prover.invariant");
  test "an element changed through a lend that keeps its invariant proves" (fun () ->
      proven Fixtures.Prover.element_changed_through_a_lend_that_keeps_its);
  test "a lent part meets its invariant" (fun () ->
      not_proven Fixtures.Prover.lent_part_meets_its_invariant "prover.invariant");
  test "a loop keeps the validity of each value it changes" (fun () ->
      proven Fixtures.Prover.loop_keeps_the_validity_of_each_value_it_changes);
  test "an iteration must keep the validity of each value the loop changes" (fun () ->
      not_proven Fixtures.Prover.iteration_must_keep_the_validity_of_each_value_the
        "prover.invariant")

(* Each expression runs once, and its changes are kept *)

let () =
  test "a guessed measure is not read from a condition with a mut argument" (fun () ->
      not_proven Fixtures.Prover.guessed_measure_is_not_read_from_a_condition_with
        "prover.termination");
  test "a mut slice's bounds are evaluated once" (fun () ->
      not_proven Fixtures.Prover.mut_slices_bounds_are_evaluated_once "prover.ensures");
  test "a while condition's mut argument changes the loop's state" (fun () ->
      not_proven Fixtures.Prover.while_conditions_mut_argument_changes_the_loops "prover.ensures");
  test "a match mut binding is written back to the scrutinee" (fun () ->
      not_proven Fixtures.Prover.match_mut_binding_is_written_back_to_the_scrutinee "prover.ensures");
  test "a while condition's cost is the iteration's" (fun () ->
      not_proven Fixtures.Prover.while_conditions_cost_is_the_iterations "prover.cost");
  test "the right operand of || is counted at its cost" (fun () ->
      not_proven Fixtures.Prover.right_operand_of_is_counted_at_its_cost "prover.cost");
  test "a call through an alias of a function value counts as a call of it" (fun () ->
      not_proven Fixtures.Prover.call_through_an_alias_of_a_function_value_counts "prover.cost");
  test "a match mut binding's new value is in the scrutinee after the arm" (fun () ->
      proven Fixtures.Prover.match_mut_bindings_new_value_is_in_the_scrutinee)

(* A function value's requires *)

let () =
  test "a function with a requires bound to a local must accept every argument" (fun () ->
      not_proven Fixtures.Prover.function_with_a_requires_bound_to_a_local_must "prover.requires");
  test "a function with a requires passed through a local must accept every argument" (fun () ->
      not_proven Fixtures.Prover.function_with_a_requires_passed_through_a_local "prover.requires");
  test "a callback's requires names a mut parameter as the caller passed it" (fun () ->
      not_proven Fixtures.Prover.callbacks_requires_names_a_mut_parameter_as_the "prover.requires");
  test "a forwarded callback must be promised its requires" (fun () ->
      not_proven Fixtures.Prover.forwarded_callback_must_be_promised_its_requires "prover.requires");
  test "a call through a function value gives a valid result" (fun () ->
      proven Fixtures.Prover.call_through_a_function_value_gives_a_valid_result);
  test "a lambda returns a valid value" (fun () ->
      not_proven Fixtures.Prover.lambda_returns_a_valid_value "prover.invariant");
  test "a callback with a requires bound to a local must accept every argument" (fun () ->
      not_proven Fixtures.Prover.callback_with_a_requires_bound_to_a_local_must "prover.requires")

(* Recursion through traits *)

let () =
  test "provided methods that call each other are recursion" (fun () ->
      only_code Fixtures.Prover.provided_methods_that_call_each_other_are "prover.termination");
  test "a call through any that reaches back is recursion" (fun () ->
      only_code Fixtures.Prover.call_through_any_that_reaches_back_is_recursion "prover.termination");
  test "a method that calls itself through any is recursion" (fun () ->
      not_proven Fixtures.Prover.method_that_calls_itself_through_any_is_recursion
        "prover.termination")

(* Constants *)

let () =
  test "a constant's value is well defined" (fun () ->
      not_proven "let shifted: UInt8 = 1 << 8\n" "prover.shift");
  test "a constant whose value is in range proves" (fun () ->
      proven "let shifted: UInt8 = 1 << 7\n")

(* Integer operations of the intrinsic module *)

let () =
  test "generic negation needs the trait method's precondition" (fun () ->
      not_proven Fixtures.Prover.generic_negation_needs_the_trait_methods "prover.requires");
  test "generic negation proves where the trait method's precondition holds" (fun () ->
      proven Fixtures.Prover.generic_negation_proves_where_the_trait_methods)

(* Text literals *)

let () =
  test "two literals with the same text are the same value" (fun () ->
      proven Fixtures.Prover.two_literals_with_the_same_text_are_the_same_value);
  test "two literals with different text are different values" (fun () ->
      not_proven Fixtures.Prover.two_literals_with_different_text_are_different "prover.ensures");
  test "a map built with a literal key contains the same literal" (fun () ->
      proven Fixtures.Prover.map_built_with_a_literal_key_contains_the_same)

(* Bitwise operations *)

let () =
  test "a bit set below a symbolic width keeps the bits above it clear" (fun () ->
      proven Fixtures.Prover.bit_set_below_a_symbolic_width_keeps_the_bits);
  test "an exclusive or may be below its first operand" (fun () ->
      not_proven Fixtures.Prover.exclusive_or_may_be_below_its_first_operand "prover.ensures")

(* Derived implementations *)

let () =
  test "a derived ordering is the one a law of another trait reads" (fun () ->
      proven Fixtures.Prover.derived_ordering_is_the_one_a_law_of_another_trait)

(* Equality through written impls *)

let () =
  test "a derived equality compares a list field as the list's equal does" (fun () ->
      proven Fixtures.Prover.derived_equality_compares_a_list_field_as_the);
  test "a law reads an impl of Equal whose bounds hold in the impl it is proven for" (fun () ->
      proven Fixtures.Prover.law_reads_an_impl_of_equal_whose_bounds_hold_in)

(* Amortized moves and copies *)

let () =
  test "a deque's potential pays for moving half of one list to the other" (fun () ->
      proven Fixtures.Prover.deques_potential_pays_for_moving_half_of_one_list);
  test "a copy pays for the potential it makes" (fun () ->
      proven Fixtures.Prover.copy_pays_for_the_potential_it_makes);
  test "a loop of pushed copies is amortized over the copies' time" (fun () ->
      proven Fixtures.Prover.loop_of_pushed_copies_is_amortized_over_the_copies)

(* Bodies across packages *)

(* The diagnostics of [app::main], in a package that depends on [lib], whose
   one module is [lib::numbers]. *)
let across library program =
  let database =
    Support.setup
      ~dependencies:[ ("app", "lib") ]
      [ ("lib::numbers", library); ("app::main", "use lib::numbers\n\n" ^ program) ]
  in
  check database (Support.file_of "app::main")

let public_doubling ensures =
  Printf.sprintf
    "public fn double(limit_count: Int64) -> Int64\n\
    \  requires limit_count < 1000 && limit_count > -1000\n\
     %s  cost time O(1)\n\
     {\n\
    \  limit_count * 2\n\
     }\n"
    ensures

let () =
  test "a caller in another package reads its callee's contract" (fun () ->
      match
        across
          (public_doubling "  ensures result == limit_count * 2\n")
          Fixtures.Prover.caller_in_another_package_reads_its_callees
      with
      | [] -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual)));
  test "a call in another package is not run" (fun () ->
      match across (public_doubling "") Fixtures.Prover.call_in_another_package_is_not_run with
      | [ _ ] -> ()
      | actual -> fail "%d diagnostics" (List.length actual))
(* Plain and amortized bounds together *)

let () =
  test "a recursive function proves a plain and an amortized bound, each by its own counting"
    (fun () -> proven Fixtures.Prover.recursive_function_proves_a_plain_and_an_amortized)

(* Clauses in other files *)

let () =
  test "a callee's clause in another file is named by its file and line" (fun () ->
      let actual = message Fixtures.Prover.callees_clause_in_another_file_is_named_by_its in
      if not (contains actual "The clause that must hold is at `standard/list/list.truss:") then
        fail "message %S" actual)
(* Collections from another package *)

let () =
  test "an insertion into a set of integers is amortized in its length" (fun () ->
      proven Fixtures.Prover.insertion_into_a_set_of_integers_is_amortized_in);
  test "an insertion into a set of any elements is amortized in their comparisons" (fun () ->
      proven Fixtures.Prover.insertion_into_a_set_of_any_elements_is_amortized);
  test "a list filled with integers is linear in its count" (fun () ->
      proven Fixtures.Prover.list_filled_with_integers_is_linear_in_its_count)

(* Fixes *)

let () =
  test "a callee's requires about the caller's parameters is offered as the caller's" (fun () ->
      let database =
        Support.setup
          [ ("app::main", Fixtures.Prover.callees_requires_about_the_callers_parameters_is) ]
      in
      match check database (Support.file_of "app::main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count < 100`" -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    String.concat ", "
                      (List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes))
                  actual)))

(* Facts under a quantifier *)

let () =
  test "a fact made in a quantifier's body is a hypothesis of the goal" (fun () ->
      proven Fixtures.Prover.fact_made_in_a_quantifiers_body_is_a_hypothesis_of);
  test "a bitwise operation under a quantifier is defined for each bound value" (fun () ->
      proven Fixtures.Prover.bitwise_operation_under_a_quantifier_is_defined);
  test "a fact made in a quantifier's body proves nothing false" (fun () ->
      not_proven Fixtures.Prover.fact_made_in_a_quantifiers_body_proves_nothing "prover.ensures")

(* Contracts under a quantifier *)

let () =
  test "a callee's ensures under its requires holds for every bound value" (fun () ->
      proven Fixtures.Prover.callees_ensures_under_its_requires_holds_for_every)

(* Early exits from concurrent loops *)

let () =
  test "a concurrent for may return early, with a value known by its type" (fun () ->
      proven Fixtures.Prover.concurrent_for_may_return_early_with_a_value_known);
  test "a value returned from a concurrent for is not known to be any one iteration's" (fun () ->
      not_proven Fixtures.Prover.value_returned_from_a_concurrent_for_is_not_known "prover.ensures")

(* Overflow fixes *)

let () =
  let fix_titles text =
    let database = Support.setup [ ("app::main", text) ] in
    List.concat_map
      (fun (diagnostic : Diagnostic.t) ->
        List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes)
      (check database (Support.file_of "app::main"))
  in
  test "a divisor that may be zero offers a requires that it is not" (fun () ->
      match fix_titles Fixtures.Prover.divisor_that_may_be_zero_offers_a_requires_that_it with
      | [ "Add `requires parts != 0`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "a shift amount that may be too large offers a requires below the width" (fun () ->
      match fix_titles Fixtures.Prover.shift_amount_that_may_be_too_large_offers_a with
      | [ "Add `requires by < 64`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "an overflow with a literal offers the bound as a requires" (fun () ->
      let database =
        Support.setup
          [ ("app::main", Fixtures.Prover.overflow_with_a_literal_offers_the_bound_as_a) ]
      in
      match check database (Support.file_of "app::main") with
      | [ { fixes = [ { title; _ } ]; _ } ] when title = "Add `requires count <= 254`" -> ()
      | actual ->
          fail "%s"
            (String.concat "; "
               (List.map
                  (fun (diagnostic : Diagnostic.t) ->
                    String.concat ", "
                      (List.map (fun (fix : _ Diagnostic.fix) -> fix.title) diagnostic.fixes))
                  actual)));
  test "a failed assert about the parameters offers it as a requires" (fun () ->
      match fix_titles Fixtures.Prover.failed_assert_about_the_parameters_offers_it_as_a with
      | [ "Add `requires low < high`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "a failed assert under an if offers the if's condition as a premise" (fun () ->
      match fix_titles Fixtures.Prover.failed_assert_under_an_if_offers_the_ifs_condition with
      | [ "Add `requires (flag) ==> (count > 0)`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "a failed assert with arithmetic offers it as a requires" (fun () ->
      match fix_titles Fixtures.Prover.failed_assert_with_arithmetic_offers_it_as_a with
      | [ "Add `requires low + 2 * high <= 100 - (high - low)`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "an unsigned sum that may overflow offers only its upper bound" (fun () ->
      match fix_titles Fixtures.Prover.unsigned_sum_that_may_overflow_offers_only_its with
      | [ "Add `requires count + other <= 255`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "an unsigned difference that may overflow offers only its lower bound" (fun () ->
      match fix_titles Fixtures.Prover.unsigned_difference_that_may_overflow_offers_only with
      | [ "Add `requires 0 <= high - low`" ] -> ()
      | actual -> fail "%s" (String.concat "; " actual));
  test "a failed assert about a call's result offers no requires" (fun () ->
      let database =
        Support.setup
          [ ("app::main", Fixtures.Prover.failed_assert_about_a_calls_result_offers_no) ]
      in
      match check database (Support.file_of "app::main") with
      | [ { code; fixes = []; _ } ] when Diagnostic.Code.name code = "prover.assertion" -> ()
      | actual -> fail "%d diagnostics" (List.length actual));
  test "an overflow names the fixes that change the code's semantics" (fun () ->
      let actual = message Fixtures.Prover.overflow_names_the_fixes_that_change_the_codes in
      if not (contains actual "checked operation") then fail "message %S" actual)

(* Counterexample paths *)

let () =
  test "a counterexample says which way each if on its path goes" (fun () ->
      let actual = message Fixtures.Prover.counterexample_says_which_way_each_if_on_its_path in
      if not (contains actual "On that path, `up` is true, `count > 100` is true.") then
        fail "message %S" actual);
  test "a counterexample says which arm of a match its path takes" (fun () ->
      let actual = message Fixtures.Prover.counterexample_says_which_arm_of_a_match_its_path in
      if not (contains actual "On that path, the arm `Some(count)` is taken.") then
        fail "message %S" actual)

(* Ranges under a quantifier *)

let () =
  test "a pure call's result is in its type's range for every bound value" (fun () ->
      proven Fixtures.Prover.pure_calls_result_is_in_its_types_range_for_every)

(* Lambdas under a quantifier *)

let () =
  test "a lambda in a quantifier that captures a bound value is known for each one" (fun () ->
      proven Fixtures.Prover.lambda_in_a_quantifier_that_captures_a_bound_value);
  test "a lambda in a quantifier that captures no bound value is known for every argument"
    (fun () -> proven Fixtures.Prover.lambda_in_a_quantifier_that_captures_no_bound)

(* Maps from another package *)

let () =
  test "an insertion into a map, of a new key or one it has, is amortized" (fun () ->
      proven Fixtures.Prover.insertion_into_a_map_of_a_new_key_or_one_it_has_is)

(* Lambdas inside lambdas *)

let applying = Fixtures.Prover.applying

let () =
  test "a lambda with a functional lambda inside that captures nothing it made is known" (fun () ->
      proven (applying ^ Fixtures.Prover.lambda_with_a_functional_lambda_inside_that));
  test "a lambda with a functional lambda inside that captures its argument is known" (fun () ->
      proven (applying ^ Fixtures.Prover.lambda_with_a_functional_lambda_inside_that_2));
  test "a functional lambda inside that captures the argument is not one function" (fun () ->
      not_proven
        (applying ^ Fixtures.Prover.functional_lambda_inside_that_captures_the)
        "prover.ensures")

(* Definitions under a quantifier *)

let () =
  test "a contract with branches, called under a quantifier on no bound value, holds there"
    (fun () -> proven Fixtures.Prover.definition_with_branches_called_under_a_quantifier);
  test "a derived ordering of a one-field record is its field's, for every value" (fun () ->
      proven Fixtures.Prover.derived_ordering_of_a_one_field_record_is_its);
  test "a derived ordering compares fields in order, for every value" (fun () ->
      proven Fixtures.Prover.derived_ordering_compares_fields_in_order_for)

(* Counts of bits *)

let () =
  test "zero has no ones" (fun () -> proven Fixtures.Prover.zero_has_no_ones);
  test "the ones of a value fit below its bit length" (fun () ->
      proven Fixtures.Prover.ones_of_a_value_fit_below_its_bit_length);
  test "the lowest one is below the bit length" (fun () ->
      proven Fixtures.Prover.lowest_one_is_below_the_bit_length);
  test "every one below a power of two is counted" (fun () ->
      proven Fixtures.Prover.every_one_below_a_power_of_two_is_counted);
  test "a value may have ones" (fun () ->
      not_proven Fixtures.Prover.value_may_have_ones "prover.ensures")

(* Proofs of laws *)

let () =
  test "a proof for a generic impl names its own generic parameters" (fun () ->
      proven Fixtures.Prover.proof_for_a_generic_impl_names_its_own_generic);
  test "a law's proof names the law's parameters, where its requires hold" (fun () ->
      proven Fixtures.Prover.laws_proof_names_the_laws_parameters_where_its)

(* Concurrent code *)

let early_return ensures =
  "fn f(first: mut Int64, second: mut Int64) -> Int64\n  requires second < 100\n" ^ ensures
  ^ "  uses Tasks\n{\n  concurrent {\n    return 0\n    second += 1\n  }\n}\n"

let () =
  test "an early exit from a concurrent block waits for the other branches" (fun () ->
      proven (early_return "  ensures second == old(second) + 1\n"));
  test "an early exit from a concurrent block sees the other branches' changes" (fun () ->
      not_proven (early_return "  ensures second == old(second)\n") "prover.ensures");
  test "a concurrent block with no early exit is read as its branches in order" (fun () ->
      proven Fixtures.Prover.concurrent_block_with_no_early_exit_is_read_as_its)

(* Diagnostics *)

let () =
  test "a counterexample gives the values of the locals where it fails" (fun () ->
      let text = message Fixtures.Prover.counterexample_gives_the_values_of_the_locals in
      if not (contains text "`at` is") then fail "%s" text);
  test "a file's proof states list proven and unproven obligations" (fun () ->
      let database =
        Support.setup [ ("app::main", Fixtures.Prover.files_proof_states_list_proven_and_unproven) ]
      in
      let states =
        Prover.states ~record:(Support.record database) database solver
          (Support.file_of "app::main")
      in
      let failed =
        List.filter (fun (state : Diagnostic.span Prover.state) -> state.failure <> None) states
      in
      if List.length failed <> 1 || List.length states < 2 then
        fail "%d states, %d failed" (List.length states) (List.length failed));
  test "a call's requires that may not hold has a note at the clause" (fun () ->
      let text = Fixtures.Prover.calls_requires_that_may_not_hold_has_a_note_at_the in
      let database = Support.setup [ ("app::main", text) ] in
      match check database (Support.file_of "app::main") with
      | [ { notes = [ (span, _) ]; _ } ] ->
          let noted = String.sub text span.start (span.stop - span.start) in
          if noted <> "count > 0" then fail "the note is at `%s`" noted
      | actual -> fail "%s" (String.concat "; " (Support.codes actual)));
  test "the same failure on another path is reported once" (fun () ->
      let actual = codes Fixtures.Prover.same_failure_on_another_path_is_reported_once in
      if actual <> [ "prover.requires" ] then fail "%s" (String.concat ", " actual))

(* Unproven code *)

let () =
  test "a construct the prover cannot read yet" (fun () ->
      not_proven Fixtures.Prover.construct_the_prover_cannot_read_yet "prover.unsupported");
  test "a type's invariant must be well defined" (fun () ->
      not_proven "type Ratio(top: Int64, bottom: Int64)\n  invariant top / bottom > 0\n"
        "prover.division");
  test "a type's invariant is well defined given the ones before it" (fun () ->
      proven Fixtures.Prover.types_invariant_is_well_defined_given_the_ones);
  test "a cost clause's bound must be well defined" (fun () ->
      let actual = codes Fixtures.Prover.cost_clauses_bound_must_be_well_defined in
      if not (List.mem "prover.requires" actual) then fail "found [%s]" (String.concat "; " actual));
  test "a derived ordering of a record compares its fields in order" (fun () ->
      proven Fixtures.Prover.derived_ordering_of_a_record_compares_its_fields);
  test "a derived ordering compares fields in declaration order, not in the order of their names"
    (fun () -> proven Fixtures.Prover.derived_ordering_compares_fields_in_declaration);
  test "a derived ordering of a record falls to the next field on a tie" (fun () ->
      proven Fixtures.Prover.derived_ordering_of_a_record_falls_to_the_next);
  test "a derived ordering of a sum orders by variant first" (fun () ->
      proven Fixtures.Prover.derived_ordering_of_a_sum_orders_by_variant_first);
  test "a derived ordering is not the reverse of itself" (fun () ->
      not_proven Fixtures.Prover.derived_ordering_is_not_the_reverse_of_itself "prover.ensures");
  test "recursion on an element of a field's list ends" (fun () ->
      proven Fixtures.Prover.recursion_on_an_element_of_a_fields_list_ends);
  test "recursion on a value that is not a part does not end" (fun () ->
      not_proven Fixtures.Prover.recursion_on_a_value_that_is_not_a_part_does_not
        "prover.termination");
  test "a trait's provided body keeps the trait's clauses on its own" (fun () ->
      not_proven Fixtures.Prover.traits_provided_body_keeps_the_traits_clauses_on "prover.ensures");
  test "a trait's provided body that keeps its clauses proves" (fun () ->
      proven Fixtures.Prover.traits_provided_body_that_keeps_its_clauses_proves);
  test "a call of a bound's method spends the time of that method" (fun () ->
      proven Fixtures.Prover.call_of_a_bounds_method_spends_the_time_of_that);
  test "the time of a bound's method is not free" (fun () ->
      let actual = codes Fixtures.Prover.time_of_a_bounds_method_is_not_free in
      if not (List.mem "prover.cost" actual) then fail "found [%s]" (String.concat "; " actual));
  test "log of a number is its bit length" (fun () ->
      proven Fixtures.Prover.log_of_a_number_is_its_bit_length);
  test "log of a bounded integer is at most its width" (fun () ->
      proven Fixtures.Prover.log_of_a_bounded_integer_is_at_most_its_width);
  test "power of two numbers is their power" (fun () ->
      proven Fixtures.Prover.power_of_two_numbers_is_their_power);
  test "a slice changed through a call changes its run of the list" (fun () ->
      proven ("" ^ Fixtures.Prover.slice_changed_through_a_call_changes_its_run_of));
  test "a slice changed through a call changes nothing more than it says" (fun () ->
      not_proven
        ("" ^ Fixtures.Prover.slice_changed_through_a_call_changes_nothing_more)
        "prover.ensures");
  test "an unsigned left shift that fits multiplies by a power of two" (fun () ->
      proven Fixtures.Prover.unsigned_left_shift_that_fits_multiplies_by_a);
  test "an unsigned right shift divides by a power of two" (fun () ->
      proven Fixtures.Prover.unsigned_right_shift_divides_by_a_power_of_two);
  test "a left shift that may not fit is not known to multiply" (fun () ->
      not_proven Fixtures.Prover.left_shift_that_may_not_fit_is_not_known_to "prover.ensures");
  test "a loop that changes a slice of any elements under a cost clause" (fun () ->
      proven Fixtures.Prover.loop_that_changes_a_slice_of_any_elements_under_a);
  test "a quantifier's body must be well defined" (fun () ->
      not_proven Fixtures.Prover.quantifiers_body_must_be_well_defined "prover.requires");
  test "a quantifier's body within its range is well defined" (fun () ->
      proven Fixtures.Prover.quantifiers_body_within_its_range_is_well_defined);
  test "a call under a quantifier gives a value for each value, not one for all" (fun () ->
      not_proven Fixtures.Prover.call_under_a_quantifier_gives_a_value_for_each "prover.ensures");
  test "alternatives bind each name to the part that matched" (fun () ->
      proven Fixtures.Prover.alternatives_bind_each_name_to_the_part_that)

(* Queries *)

let () =
  (* A query of one integer whose goal compares it with itself. A query's
     text names its symbols canonically, so two of these differ only in
     their operators, and each test of the cache uses an operator no other
     test does, so that no other test has solved its query in this
     process. *)
  let compared_with_itself operator =
    let symbol = Logic.Symbol.Variable { label = "compared"; numbers = [] } in
    {
      Logic.declarations = [ Logic.Constant (symbol, Logic.Int) ];
      facts = [];
      goal = Logic.Operation (operator, [ Logic.Symbol symbol; Logic.Symbol symbol ]);
    }
  in
  test "an answer in the cache is read, and the solver is not run" (fun () ->
      let query = compared_with_itself ">=" in
      let request = Solver.request query in
      let cache =
        {
          Solver.find =
            (fun key -> if key = Solver.request_key request then Some "proven\n" else None);
          add = (fun _ _ -> fail "kept an answer the cache already had");
        }
      in
      match Solver.find ~cache () with
      | Error message -> fail "%s" message
      | Ok solver ->
          if
            Solver.read request (List.hd (Solver.solve_all solver [ (request, query) ]))
            <> Solver.Proven
          then fail "expected the cached answer";
          if Solver.queries_run solver <> 0 then fail "ran the solver");
  test "a solved answer is added to the cache under its request's key" (fun () ->
      let query = compared_with_itself "<=" in
      let request = Solver.request query in
      let cached_answers = Hashtbl.create 1 in
      let cache =
        { Solver.find = Hashtbl.find_opt cached_answers; add = Hashtbl.replace cached_answers }
      in
      match Solver.find ~cache () with
      | Error message -> fail "%s" message
      | Ok solver ->
          ignore (Solver.solve_all solver [ (request, query) ]);
          if Solver.queries_run solver <> 1 then fail "did not run the solver";
          if Hashtbl.find_opt cached_answers (Solver.request_key request) <> Some "proven\n" then
            fail "the cache does not have the answer");
  test "a query's text names nothing by its Truss name" (fun () ->
      let database =
        Support.setup [ ("app::main", Fixtures.Prover.querys_text_names_nothing_by_its_truss_name) ]
      in
      let key =
        List.hd (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
      in
      match Query.demand database Prover.proof (Resolve.Names.key_of key) with
      | Obligations { obligations = [ obligation ]; _ } ->
          let text = Logic.text obligation.query in
          if contains text "count" then fail "the text names `count`: %s" text
      | _ -> fail "expected one obligation");
  test "renaming a function and its parameter gives the same query" (fun () ->
      let key_of text =
        let database = Support.setup [ ("app::main", text) ] in
        let key =
          List.hd (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
        in
        match Query.demand database Prover.proof (Resolve.Names.key_of key) with
        | Obligations { obligations = [ obligation ]; _ } -> Solver.For_testing.key obligation.query
        | _ -> "none"
      in
      let first = key_of Fixtures.Prover.renaming_a_function_and_its_parameter_gives_the in
      let second = key_of Fixtures.Prover.renaming_a_function_and_its_parameter_gives_the_2 in
      if first <> second || first = "none" then fail "%s and %s" first second)

(* Arrays *)

let () =
  test "a slice of a whole array is within it" (fun () ->
      proven Fixtures.Prover.slice_of_a_whole_array_is_within_it);
  test "a loop that changes an array's elements keeps their potentials" (fun () ->
      proven Fixtures.Prover.loop_that_changes_an_arrays_elements_keeps_their);
  test "a slice of an array is within it only as far as its count" (fun () ->
      not_proven Fixtures.Prover.slice_of_an_array_is_within_it_only_as_far_as_its "prover.requires")

(* Deep definitions *)

let () =
  test "a nested call's arguments are written once, however deep it nests" (fun () ->
      let most depth =
        let nested =
          List.fold_left
            (fun inner _ -> "spread(" ^ inner ^ ")")
            "value + 12345 - 12345" (List.init depth Fun.id)
        in
        let database =
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
              Path.show declaration.path = "app::main::f")
            (Query.demand database Resolve.Names.declarations (Support.module_of "app::main"))
        in
        match Query.demand database Prover.proof (Resolve.Names.key_of key) with
        | Obligations { obligations; _ } ->
            List.fold_left
              (fun most (obligation : Prover.Translate.obligation) ->
                let text = Logic.text obligation.query in
                let rec count from actual =
                  match String.index_from_opt text from '1' with
                  | Some at when at + 5 <= String.length text && String.sub text at 5 = "12345" ->
                      count (at + 5) (actual + 1)
                  | Some at -> count (at + 1) actual
                  | None -> actual
                in
                max most (count 0 0))
              0 obligations
        | _ ->
            fail "expected obligations";
            0
      in
      let shallow = most 3 and deep = most 6 in
      if deep > shallow then fail "written %d times nested 3 deep, %d times 6 deep" shallow deep);
  test "a callee is known by its contract, not its body" (fun () ->
      not_proven Fixtures.Prover.callee_with_an_ensures_is_known_by_its_contract "prover.ensures");
  test "a contract that states the body gives what the body would" (fun () ->
      proven Fixtures.Prover.contract_that_states_the_body_gives_what_the_body)

(* Triggers *)

let variable label = Logic.Symbol.Variable { label; numbers = [] }

let triggered fact =
  let open Logic in
  Logic.text
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
    let text = triggered fact in
    if not (contains text fragment) then fail "expected %s in %s" fragment text
  in
  test "a quantified fact triggers on an application of its variable" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int) ],
             Operation (">=", [ i_term; int 0 ]) ==> positive (applied_f i_term) ))
        ":pattern ((x0 b0))");
  test "a trigger has no arithmetic on a bound variable" (fun () ->
      let text =
        triggered
          (forall
             ([ (variable "i", Int) ], positive (applied_f (Operation ("+", [ i_term; int 1 ])))))
      in
      if contains text ":pattern" then fail "%s" text);
  test "a trigger that would match its own body's larger term is passed over" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int) ],
             Operation ("<", [ applied_f i_term; applied_f (Operation ("+", [ i_term; int 1 ])) ])
             &&& positive (applied_g i_term) ))
        ":pattern ((x2 b0)))");
  test "a definition triggers on the term it defines" (fun () ->
      let text =
        triggered
          (forall
             ( [ (variable "i", Int) ],
               equal (applied_f i_term) (Operation ("+", [ applied_g i_term; int 1 ])) ))
      in
      if (not (contains text ":pattern ((x0 b0)))")) || contains text ":pattern ((x1" then
        fail "%s" text);
  let query fact =
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
  test "a quantified fact with no trigger is told apart" (fun () ->
      if
        not
          (untriggered
             (query
                (forall
                   ( [ (variable "i", Int) ],
                     positive (applied_f (Operation ("+", [ i_term; int 1 ]))) ))))
      then fail "a fact on f(i + 1) alone has no trigger";
      if untriggered (query (forall ([ (variable "i", Int) ], positive (applied_f i_term)))) then
        fail "a fact on f(i) has one");
  test "variables named by no one application share a trigger" (fun () ->
      expect
        (forall
           ( [ (variable "i", Int); (variable "j", Int) ],
             Operation ("<", [ applied_f i_term; applied_g j_term ]) ))
        ":pattern ((x0 b0) (x2 b1))");
  let patterns text =
    let rec count occurrence =
      match Substring.find ~occurrence text ":pattern" with
      | Some _ -> count (occurrence + 1)
      | None -> occurrence - 1
    in
    count 1
  in
  test "transitivity triggers on all three of its applications" (fun () ->
      let k_term = Symbol (variable "k") in
      let at_most first second =
        Operation ("<=", [ Apply (variable "h", [ first; second ]); int 0 ])
      in
      let text =
        triggered
          (forall
             ( [ (variable "i", Int); (variable "j", Int); (variable "k", Int) ],
               at_most i_term j_term &&& at_most j_term k_term ==> at_most i_term k_term ))
      in
      if patterns text <> 1 || not (contains text ":pattern ((x2 b0 b1) (x2 b0 b2) (x2 b1 b2))")
      then fail "%s" text);
  test "an equation between two applications triggers on either" (fun () ->
      let text =
        triggered (forall ([ (variable "i", Int) ], equal (applied_f i_term) (applied_g i_term)))
      in
      if patterns text <> 2 then fail "%s" text)

(* Short-circuit operators *)

let bump = Fixtures.Prover.bump

let () =
  test "a change on the right of && happens only where the left holds" (fun () ->
      proven (bump ^ Fixtures.Prover.change_on_the_right_of_happens_only_where_the_left));
  test "a change on the right of || is not known to have happened" (fun () ->
      not_proven
        (bump ^ Fixtures.Prover.change_on_the_right_of_is_not_known_to_have)
        "prover.ensures")

(* Function values in the logic *)

let apply_function = Fixtures.Prover.apply_function

let () =
  test "a pure function value gives the same result for the same argument" (fun () ->
      proven Fixtures.Prover.pure_function_value_gives_the_same_result_for_the);
  test "a function value that uses a capability may give different results" (fun () ->
      not_proven Fixtures.Prover.function_value_that_uses_a_capability_may_give "prover.ensures");
  test "a function value without a time clause is a fresh result" (fun () ->
      not_proven Fixtures.Prover.function_value_without_a_time_clause_is_a_fresh "prover.ensures");
  test "a lambda applied is its body" (fun () ->
      proven (apply_function ^ Fixtures.Prover.lambda_applied_is_its_body));
  test "a lambda whose body is not its definition gives its body's facts" (fun () ->
      proven (apply_function ^ Fixtures.Prover.lambda_whose_body_is_not_its_definition_gives_its));
  test "a lambda body's facts are about its own argument" (fun () ->
      not_proven
        (apply_function ^ Fixtures.Prover.lambda_bodys_facts_are_about_its_own_argument)
        "prover.ensures");
  let halved = Fixtures.Prover.halved in
  test "a named function with a requires, as a value, keeps its ensures" (fun () ->
      proven (halved ^ Fixtures.Prover.named_function_with_a_requires_as_a_value_keeps));
  test "a named function, as a value, gives no more than its ensures" (fun () ->
      not_proven
        (halved ^ Fixtures.Prover.named_function_as_a_value_gives_no_more_than_its)
        "prover.ensures");
  test "a lambda applied knows its captures" (fun () ->
      proven (apply_function ^ Fixtures.Prover.lambda_applied_knows_its_captures));
  test "two lambdas with the same body are the same function" (fun () ->
      proven Fixtures.Prover.two_lambdas_with_the_same_body_are_the_same);
  test "lambdas with different bodies are not known to be the same function" (fun () ->
      not_proven Fixtures.Prover.lambdas_with_different_bodies_are_not_known_to_be "prover.ensures");
  test "a named pure function applied is the function" (fun () ->
      proven
        (Fixtures.Prover.named_pure_function_applied_is_the_function ^ apply_function
       ^ Fixtures.Prover.named_pure_function_applied_is_the_function_2))

let () =
  test "a specification spends nothing, whatever it calls" (fun () ->
      proven Fixtures.Prover.specification_spends_nothing_whatever_it_calls)

(* Sums over sequences *)

let () =
  test "appending adds the new element's measure to a sum" (fun () ->
      proven Fixtures.Prover.appending_adds_the_new_elements_measure_to_a_sum);
  test "a sum is not known to be anything else" (fun () ->
      not_proven Fixtures.Prover.sum_is_not_known_to_be_anything_else "prover.ensures");
  test "a loop whose iterations cost different amounts is bounded by a sum" (fun () ->
      proven Fixtures.Prover.loop_whose_iterations_cost_different_amounts_is);
  test "a loop's bound that leaves out its iterations' sum does not hold" (fun () ->
      not_proven Fixtures.Prover.loops_bound_that_leaves_out_its_iterations_sum "prover.cost")

(* Incremental work: after an edit, which definitions are proven again,
   and how many queries reach the solver rather than its cache. Each test's
   definitions are its own, so no other test has solved its queries. *)

let again before after =
  let solver = Lazy.force Support.solver in
  let database = Support.setup [ ("app::main", before) ] in
  let file = Support.file_of "app::main" in
  let engine = Engine.of_context database in
  let prove () =
    match Checks.diagnostics database file with
    | [] -> Prover.diagnostics ~record:(Support.record database) database solver file
    | errors -> errors
  in
  (match prove () with
  | [] -> ()
  | actual -> fail "before the edit: %s" (String.concat "; " (Support.codes actual)));
  Database.For_testing.set_text engine file after;
  Engine.For_testing.clear_log engine;
  let runs_before = Solver.queries_run solver in
  (match prove () with
  | [] -> ()
  | actual -> fail "after the edit: %s" (String.concat "; " (Support.codes actual)));
  let proven =
    List.filter_map
      (fun (key : Resolve.Names.key) ->
        if key.module_ = file.module_ then
          match key.path with Top { name; _ } -> Some name | path -> Some (Path.show path)
        else None)
      (Engine.For_testing.computed engine Prover.proof)
  in
  (List.sort_uniq compare proven, Solver.queries_run solver - runs_before)

let expect_again before after ~proven ~solved =
  let actual, count = again before after in
  if actual <> proven || count <> solved then
    fail "proven again: [%s], with %d queries solved; expected [%s], with %d"
      (String.concat ", " actual) count (String.concat ", " proven) solved

let () =
  test "editing a body proves that definition again and no other" (fun () ->
      let text index =
        Printf.sprintf
          "fn last_reading(readings: List[Int32]) -> Int32\n\
          \  requires readings.length() > 2\n\
           {\n\
          \  readings[%s]\n\
           }\n\n\
           fn next_reading(reading: UInt16) -> UInt16\n\
          \  requires reading < 900\n\
           {\n\
          \  reading + 7\n\
           }\n"
          index
      in
      expect_again (text "1") (text "2") ~proven:[ "last_reading" ] ~solved:1);
  test "renaming a local solves nothing again" (fun () ->
      let text name =
        Printf.sprintf
          "fn first_sample(samples: List[Int16]) -> Int16\n\
          \  requires samples.length() > 0\n\
           {\n\
          \  let %s = samples[0]\n\
          \  %s\n\
           }\n"
          name name
      in
      expect_again (text "first") (text "head") ~proven:[ "first_sample" ] ~solved:0);
  test "editing a callee's ensures proves its callers again" (fun () ->
      let text ensures =
        Printf.sprintf
          "fn halve(amount: UInt32) -> UInt32\n\
          \  ensures %s\n\
           {\n\
          \  amount / 2\n\
           }\n\n\
           fn halve_and_add(amount: UInt32) -> UInt32 {\n\
          \  halve(amount) + 1\n\
           }\n\n\
           fn unrelated(level: UInt32) -> UInt32\n\
          \  requires level < 10\n\
           {\n\
          \  level + 1\n\
           }\n"
          ensures
      in
      expect_again (text "result < 4000000000") (text "result <= amount / 2")
        ~proven:[ "halve"; "halve_and_add" ] ~solved:2)

(* Addresses of views *)

(* A module of the standard library, which alone can import
   [standard::intrinsic]: its diagnostics. *)
let in_standard text =
  let database = Engine.context (Engine.create ~log:true ()) in
  Database.load_package (Engine.of_context database)
    ~name:{ owner = None; name = "standard" }
    ~dependencies:[]
    [ (Support.file_of "standard::probe", text) ];
  check database (Support.file_of "standard::probe")

let proven_in_standard text =
  match in_standard text with
  | [] -> ()
  | actual ->
      fail "%s"
        (String.concat "; "
           (List.map (fun (diagnostic : Diagnostic.t) -> diagnostic.message) actual))

let () =
  test "a view of a scalar ends within the address space and is not at zero" (fun () ->
      proven_in_standard Fixtures.Prover.view_of_a_scalar_ends_within_the_address_space_and)

(* Intrinsic operations *)

let () =
  test "an intrinsic operation has its operator's facts" (fun () ->
      proven_in_standard Fixtures.Prover.intrinsic_operation_has_its_operators_facts);
  test "an intrinsic shift has its operator's obligation on the amount" (fun () ->
      match
        Support.codes (in_standard Fixtures.Prover.intrinsic_shift_has_its_operators_obligation_on)
      with
      | [ "prover.shift" ] -> ()
      | codes -> fail "expected prover.shift, found %s" (String.concat ", " codes))

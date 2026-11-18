let () =
  Codegen_support.expect_pass "calls, operators, comparisons, a let, an if, and a return"
    Fixtures.Lowering.calls_operators_let_if_and_return;
  Codegen_support.expect_pass "`let x = own y` moves the value, and `let x = y` aliases the place"
    Fixtures.Lowering.let_own_and_let_alias;
  Codegen_support.expect_pass
    "a trait method call resolves to the type's impl, or to a bound in a generic function"
    Fixtures.Lowering.trait_method_calls_through_an_impl_and_a_bound;
  Codegen_support.expect_pass
    "an assignment, a call that omits an argument with a default, and a field access"
    Fixtures.Lowering.assignment_default_argument_and_field_access

let () =
  Codegen_support.expect_pass
    "a string literal, a constant, and a constructor call with every field"
    Fixtures.Lowering.string_literal_a_constant_and_a_constructor_call

let () =
  Codegen_support.expect_pass
    "a while loop with break and continue, and a for loop over an integer range"
    Fixtures.Lowering.while_loop_with_break_and_continue_and_a_range_loop;
  Codegen_support.expect_pass "a for loop over a list" Fixtures.Lowering.for_loop_over_a_list

let () =
  Codegen_support.expect_pass "a match on literals, a range, strings, and two values at once"
    Fixtures.Lowering.match_on_literals_ranges_strings_and_pairs;
  Codegen_support.expect_pass
    "alternatives that bind a name bind it from the alternative that matched"
    Fixtures.Lowering.or_patterns_binding_a_shape_field;
  Codegen_support.expect_pass
    "a let with an else, an is-test, a guard, and a pattern in a let and in a for loop"
    Fixtures.Lowering.let_else_is_test_guard_and_patterns

let () =
  Codegen_support.expect_pass "a todo and an unreachable on paths not taken, and a proof block"
    Fixtures.Lowering.todo_unreachable_and_proof_block

let () =
  Codegen_support.expect_pass
    "an is-test on a call's result keeps the result for the names it binds"
    Fixtures.Lowering.is_test_on_a_label_call

let () =
  Codegen_support.expect_pass
    "defaults of a plain, a read-only, and an own parameter, and a requires clause"
    Fixtures.Lowering.parameter_defaults_and_a_requires;
  Codegen_support.test "a requires clause is not evaluated when a test runs" (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.step_with_a_requires_in_a_test
        "test 0 passed\n");
  Codegen_support.test "an index of a list out of bounds is reported where the index is written"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.grid_cell_index_out_of_bounds
        "test 0 panicked\nmessage 47\nindex out of bounds\n  at example/main.truss:4:3\n");
  Codegen_support.test
    "a check in a called lending method of the standard library reports the program's call site"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.map_index_by_a_missing_key
        "test 0 panicked\nmessage 48\nindex out of bounds\n  at example/main.truss:3:11\n");
  Codegen_support.test
    "a check on the first line of an indented method reports its column in the file" (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.panic_on_the_first_line_of_a_method_in_an_impl
        "test 0 panicked\nmessage 48\narithmetic overflow\n  at example/main.truss:8:28\n");
  Codegen_support.test
    "a column after a letter of two bytes counts Unicode scalar values, as a diagnostic's does"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.index_past_the_end_after_an_accented_letter
        "test 0 panicked\nmessage 48\nindex out of bounds\n  at example/main.truss:3:29\n")

let () =
  Codegen_support.expect_pass "an index, and a lending method with a default"
    Fixtures.Lowering.index_and_a_lending_method_with_a_default

let () =
  Codegen_support.expect_pass "a capability method call, a provide, and a crash on a path not taken"
    Fixtures.Lowering.capability_call_provide_and_untaken_crash;
  Codegen_support.expect_pass "a value converted to an any value, from an impl and from a bound"
    Fixtures.Lowering.any_values_from_an_impl_and_a_bound;
  Codegen_support.expect_pass "a call through any reaches the overload for its receiver's mode"
    Fixtures.Lowering.any_counter_overloaded_by_receiver

let () =
  Codegen_support.expect_pass "an interpolated string, a tagged string, and a copy"
    Fixtures.Lowering.interpolated_string_a_tagged_string_and_a_copy;
  Codegen_support.expect_pass "a set, a map, a record update, a field default, and a parallel block"
    Fixtures.Lowering.set_map_record_update_defaults_and_parallel_block

let () =
  Codegen_support.expect_pass "an array literal and a generic value parameter used as a value"
    Fixtures.Lowering.array_literal_and_a_value_parameter

let () =
  Codegen_support.test
    "a call of a lending method that never lends compiles, and the code after it is unreachable"
    (fun () ->
      Codegen_support.expect_output Fixtures.Lowering.call_of_a_lending_method_that_never_lends
        "test 0 panicked\nmessage 35\nno cell\n  at example/main.truss:6:3\n")

let () =
  Codegen_support.expect_pass "a named function as a value, at its own type and at a wider one"
    Fixtures.Lowering.named_function_as_a_value_at_two_types

let () =
  Codegen_support.expect_pass
    "a lambda that captures a local and one that captures self, called through a value"
    Fixtures.Lowering.lambdas_capturing_a_local_and_self;
  Codegen_support.expect_pass "a method called through an any value"
    Fixtures.Lowering.method_called_through_an_any_value;
  Codegen_support.expect_pass "next on a cursor and a loop over the rest of it"
    Fixtures.Lowering.next_on_a_cursor_and_a_loop_over_the_rest_of_it

let () =
  Codegen_support.expect_pass "a loop over a value of a type that implements Cursor"
    Fixtures.Lowering.loop_over_a_countdown_cursor

let () =
  Codegen_support.expect_pass "a capability method called with arguments left to their defaults"
    Fixtures.Lowering.capability_method_with_default_arguments

let () =
  Codegen_support.expect_pass
    "a capability default with arithmetic is lowered with its method's spans"
    Fixtures.Lowering.capability_default_with_arithmetic

let () =
  Codegen_support.expect_pass "a slice of a range of a list, of a slice, and with a bound left out"
    Fixtures.Lowering.slices_of_lists_and_slices

let () =
  Codegen_support.expect_pass
    "a slice of a small array, or of one in a small record, views the caller's array"
    Fixtures.Lowering.slices_of_small_arrays

let () =
  Codegen_support.expect_pass "constructors of lent places, lent read-only and `mut`"
    Fixtures.Lowering.bag_lending_numbered_constructors

let () =
  Codegen_support.expect_pass
    "a lent constructor is read, mutated, and passed whole, and its places are written back"
    Fixtures.Lowering.lent_constructor_read_mutated_and_passed_whole

let () =
  Codegen_support.expect_pass
    "a lending method that lends on several paths: places, a value it makes, and one built around \
     places"
    Fixtures.Lowering.names_lending_on_several_paths

let () =
  Codegen_support.expect_pass "a value moved out of a `mut` parameter, which is then reinitialized"
    Fixtures.Lowering.value_moved_out_of_a_mut_parameter

let () =
  Codegen_support.expect_pass
    "quantifiers over ranges, which run as loops that stop at the first answer"
    Fixtures.Lowering.quantifiers_over_ranges

let () =
  Codegen_support.expect_pass
    "quantifiers over a list, a slice, and a type with a `count` and an `element` of its own"
    Fixtures.Lowering.quantifiers_over_a_list_a_slice_and_a_shelf

let () =
  Codegen_support.expect_pass "quantifiers whose pattern leaves out the elements it does not match"
    Fixtures.Lowering.quantifiers_with_a_refutable_pattern

let () =
  Codegen_support.expect_pass
    "constants that are infinite or not a number, which C has no literal for"
    Fixtures.Lowering.infinite_and_not_a_number_constants

let () =
  Codegen_support.expect_pass "a cursor through a bound, and the methods Cursor gives it"
    Fixtures.Lowering.cursor_through_a_bound

let () =
  Codegen_support.expect_pass
    "any of a trait whose methods name an associated type, over two kinds of cursor"
    Fixtures.Lowering.any_over_two_countdown_cursors

let () =
  Codegen_support.expect_pass
    "a match that owns a sum takes one variant's payload and drops the other variant whole"
    Fixtures.Lowering.match_owning_a_problem

let () =
  Codegen_support.expect_pass "a loop over a range of characters, which has no surrogates in it"
    Fixtures.Lowering.loop_over_a_range_of_characters

let () =
  Codegen_support.expect_pass
    "a function with a default, called through a function value, uses its arguments"
    Fixtures.Lowering.scale_with_a_default_through_a_function_value

let expect_fold name ~folded ~run source =
  Codegen_support.test name (fun () ->
      let _, backend =
        Codegen_support.load
          ~roots:
            (List.map
               (fun name -> Lowered.Item.Constant (Top { module_ = Codegen_support.example; name }))
               (folded @ run))
          source
      in
      let is_folded name =
        Backend.For_testing.is_folded backend (Top { module_ = Codegen_support.example; name })
      in
      List.iter
        (fun name ->
          if not (is_folded name) then Codegen_support.fail "%s is run, and should fold" name)
        folded;
      List.iter
        (fun name -> if is_folded name then Codegen_support.fail "%s folds, and should be run" name)
        run;
      Codegen_support.expect_output source "test 0 passed\n")

let () =
  expect_fold "constants fold from their MIR, except a set, which is built by running"
    ~folded:[ "small"; "flag"; "names"; "rows"; "corner"; "primes" ]
    ~run:[ "colors" ] Fixtures.Lowering.folded_constants_and_a_set;
  expect_fold "a chain of ten constants, each naming the one before, folds" ~folded:[ "tenth" ]
    ~run:[] Fixtures.Lowering.chain_of_ten_constants

let () =
  Codegen_support.expect_pass
    "a return in an arm of a match on a lent part drops only what it holds"
    Fixtures.Lowering.return_in_a_match_on_a_json_field

module Lower = Compile.For_testing.Lower

(* Lowering from the MIR: a program for each kind of statement and
   terminator, whose test passes when the code lowered from it runs
   correctly. *)

open Codegen_support

let () =
  passes "calls, operators, comparisons, a let, an if, and a return"
    Fixtures.Lowering.calls_operators_comparisons_a_let_an_if_and_a;
  passes "`let x = own y` moves the value, and `let x = y` aliases the place"
    Fixtures.Lowering.let_x_own_y_moves_the_value_and_let_x_y_aliases;
  passes "a trait method call resolves to the type's impl, or to a bound in a generic function"
    Fixtures.Lowering.trait_method_call_resolves_to_the_types_impl_or_to;
  passes "an assignment, a call that omits an argument with a default, and a field access"
    Fixtures.Lowering.assignment_a_call_that_omits_an_argument_with_a

let () =
  passes "a string literal, a constant, and a constructor call with every field"
    Fixtures.Lowering.string_literal_a_constant_and_a_constructor_call

let () =
  passes "a while loop with break and continue, and a for loop over an integer range"
    Fixtures.Lowering.while_loop_with_break_and_continue_and_a_for_loop;
  passes "a for loop over a list" Fixtures.Lowering.for_loop_over_a_list

let () =
  passes "a match on literals, a range, strings, and two values at once"
    Fixtures.Lowering.match_on_literals_a_range_strings_and_two_values;
  passes "alternatives that bind a name bind it from the alternative that matched"
    Fixtures.Lowering.alternatives_that_bind_a_name_bind_it_from_the;
  passes "a let with an else, an is-test, a guard, and a pattern in a let and in a for loop"
    Fixtures.Lowering.let_with_an_else_an_is_test_a_guard_and_a_pattern

let () =
  passes "a todo and an unreachable on paths not taken, and a proof block"
    Fixtures.Lowering.todo_and_an_unreachable_on_paths_not_taken_and_a

let () =
  passes "an is-test on a call's result keeps the result for the names it binds"
    Fixtures.Lowering.is_test_on_a_calls_result_keeps_the_result_for_the

let () =
  passes "defaults of a plain, a read-only, and an own parameter, and a requires clause"
    Fixtures.Lowering.defaults_of_a_plain_a_read_only_and_an_own;
  test "a requires clause is not evaluated when a test runs" (fun () ->
      expect_output Fixtures.Lowering.requires_clause_is_not_evaluated_when_a_test_runs
        "test 0 passed\n");
  test "a check in a lending method of the standard library reports the program's call site"
    (fun () ->
      expect_output Fixtures.Lowering.check_in_a_lending_method_of_the_standard_library
        "test 0 panicked\nmessage 47\nindex out of bounds\n  at example/main.truss:4:3\n")

let () =
  passes "an index, and a lending method with a default"
    Fixtures.Lowering.index_and_a_lending_method_with_a_default

let () =
  passes "a capability method call, a provide, and a crash on a path not taken"
    Fixtures.Lowering.capability_method_call_a_provide_and_a_crash_on_a;
  passes "a value converted to an any value, from an impl and from a bound"
    Fixtures.Lowering.value_converted_to_an_any_value_from_an_impl_and

let () =
  passes "an interpolated string, a tagged string, and a copy"
    Fixtures.Lowering.interpolated_string_a_tagged_string_and_a_copy;
  passes "a set, a map, a record update, a field default, and a parallel block"
    Fixtures.Lowering.set_a_map_a_record_update_a_field_default_and_a

let () =
  passes "an array literal and a generic value parameter used as a value"
    Fixtures.Lowering.array_literal_and_a_generic_value_parameter_used

let () =
  test "a call of a lending method that never lends compiles, and the code after it is unreachable"
    (fun () ->
      expect_output Fixtures.Lowering.call_of_a_lending_method_that_never_lends
        "test 0 panicked\nmessage 35\nno cell\n  at example/main.truss:6:3\n")

let () =
  passes "a named function as a value, at its own type and at a wider one"
    Fixtures.Lowering.named_function_as_a_value_at_its_own_type_and_at_a

let () =
  passes "a lambda that captures a local and one that captures self, called through a value"
    Fixtures.Lowering.lambda_that_captures_a_local_and_one_that_captures;
  passes "a method called through an any value" Fixtures.Lowering.method_called_through_an_any_value;
  passes "next on a cursor and a loop over the rest of it"
    Fixtures.Lowering.next_on_a_cursor_and_a_loop_over_the_rest_of_it

let () =
  passes "a loop over a value of a type that implements Cursor"
    Fixtures.Lowering.loop_over_a_value_of_a_type_that_implements_cursor

let () =
  passes "a capability method called with arguments left to their defaults"
    Fixtures.Lowering.capability_method_called_with_arguments_left_to

let () =
  passes "a slice of a range of a list, of a slice, and with a bound left out"
    Fixtures.Lowering.slice_of_a_range_of_a_list_of_a_slice_and_with_a

let () =
  passes "a slice of a small array, or of one in a small record, views the caller's array"
    Fixtures.Lowering.slice_of_a_small_array_or_of_one_in_a_small_record

let () =
  passes "constructors of lent places, lent read-only and `mut`"
    Fixtures.Lowering.constructors_of_lent_places_lent_read_only_and

let () =
  passes "a lent constructor is read, mutated, and passed whole, and its places are written back"
    Fixtures.Lowering.lent_constructor_is_read_mutated_and_passed_whole

let () =
  passes
    "a lending method that lends on several paths: places, a value it makes, and one built around \
     places"
    Fixtures.Lowering.lending_method_that_lends_on_several_paths_places

let () =
  passes "a value moved out of a `mut` parameter, which is then reinitialized"
    Fixtures.Lowering.value_moved_out_of_a_mut_parameter_which_is_then

let () =
  passes "quantifiers over ranges, which run as loops that stop at the first answer"
    Fixtures.Lowering.quantifiers_over_ranges_which_run_as_loops_that

let () =
  passes "quantifiers over a list, a slice, and a type with a `count` and an `element` of its own"
    Fixtures.Lowering.quantifiers_over_a_list_a_slice_and_a_type_with_an

let () =
  passes "constants that are infinite or not a number, which C has no literal for"
    Fixtures.Lowering.constants_that_are_infinite_or_not_a_number_which

let () =
  passes "a cursor through a bound, and the methods Cursor gives it"
    Fixtures.Lowering.cursor_through_a_bound_and_the_methods_cursor_gives

let () =
  passes "any of a trait whose methods name an associated type, over two kinds of cursor"
    Fixtures.Lowering.any_of_a_trait_whose_methods_name_an_associated

let () =
  passes "a match that owns a sum takes one variant's payload and drops the other variant whole"
    Fixtures.Lowering.match_that_owns_a_sum_takes_one_variants_payload

let () =
  passes "a loop over a range of characters, which has no surrogates in it"
    Fixtures.Lowering.loop_over_a_range_of_characters_which_has_no

let () =
  passes "a function with a default, called through a function value, uses its arguments"
    Fixtures.Lowering.function_with_a_default_called_through_a_function

(* Checks which of a module's constants fold and which are computed by
   running their evaluators, and that the module's test passes. *)
let folds name ~folded ~run source =
  test name (fun () ->
      let database, _ = load source in
      let context =
        Lower.context ~checks:true database target_64 ~constant:(fun context path ->
            match Lower.constant context path with Folded data -> Some data.value | Run _ -> None)
      in
      let value = Lower.constant_value context in
      let constant name : Path.t = Top { module_ = example; name } in
      List.iter
        (fun name -> if value (constant name) = None then fail "%s is run, and should fold" name)
        folded;
      List.iter
        (fun name -> if value (constant name) <> None then fail "%s folds, and should be run" name)
        run;
      expect_output source "test 0 passed\n")

let () =
  folds "constants fold from their MIR, except a set, which is built by running"
    ~folded:[ "small"; "flag"; "names"; "rows"; "corner"; "primes" ]
    ~run:[ "colors" ] Fixtures.Lowering.constants_fold_except_a_set_which_is_built_by

let () =
  passes "a return in an arm of a match on a lent part drops only what it holds"
    Fixtures.Lowering.return_in_an_arm_of_a_match_on_a_lent_part_drops

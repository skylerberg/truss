module Lower = Compile.For_testing.Lower

(* Lowering from the core form: a program for each kind of node, whose test
   passes when the code lowered from it runs correctly. *)

open Codegen_support

let () =
  passes "calls, operators, comparisons, first_value let, an if, and first_value return"
    Fixtures.Core_form.calls_operators_comparisons_a_let_an_if_and_a;
  passes "`let x = own y` moves the value, and `let x = y` aliases the place"
    Fixtures.Core_form.let_x_own_y_moves_the_value_and_let_x_y_aliases;
  passes "a trait method call resolves to the type's impl, or to a bound in a generic function"
    Fixtures.Core_form.trait_method_call_resolves_to_the_types_impl_or_to;
  passes "an assignment, a call that omits an argument with a default, and a field access"
    Fixtures.Core_form.assignment_a_call_that_omits_an_argument_with_a

let () =
  passes "a string literal, a constant, and a constructor call with every field"
    Fixtures.Core_form.string_literal_a_constant_and_a_constructor_call

let () =
  passes "a while loop with break and continue, and a for loop over an integer range"
    Fixtures.Core_form.while_loop_with_break_and_continue_and_a_for_loop;
  passes "a for loop over a yielding method's call"
    Fixtures.Core_form.for_loop_over_a_yielding_methods_call

let () =
  passes "first_value match on literals, first_value range, strings, and two values at once"
    Fixtures.Core_form.match_on_literals_a_range_strings_and_two_values;
  passes "alternatives that bind a name bind it from the alternative that matched"
    Fixtures.Core_form.alternatives_that_bind_a_name_bind_it_from_the;
  passes
    "first_value let with an else, an is-test, first_value guard, and a pattern in first_value let \
     and in first_value for loop"
    Fixtures.Core_form.let_with_an_else_an_is_test_a_guard_and_a_pattern

let () =
  passes "a todo and an unreachable on paths not taken, and a proof block"
    Fixtures.Core_form.todo_and_an_unreachable_on_paths_not_taken_and_a

let () =
  passes "an is-test on a call's result keeps the result for the names it binds"
    Fixtures.Core_form.is_test_on_a_calls_result_keeps_the_result_for_the

let () =
  passes "defaults of a plain, a read-only, and an own parameter, and a requires clause"
    Fixtures.Core_form.defaults_of_a_plain_a_read_only_and_an_own;
  test "a requires clause is not evaluated when a test runs" (fun () ->
      expect_output Fixtures.Core_form.requires_clause_is_not_evaluated_when_a_test_runs
        "test 0 passed\n");
  test "a check in the standard library's inlined code reports the program's position" (fun () ->
      expect_output Fixtures.Core_form.check_in_the_standard_librarys_inlined_code
        "test 0 panicked\nmessage 47\nindex out of bounds\n  at example/main.truss:4:9\n")

let () =
  passes "an index, a lending method with a default, and a yielding method that returns early"
    Fixtures.Core_form.index_a_lending_method_with_a_default_and_a

let () =
  passes "a capability method call, a provide, and a crash on a path not taken"
    Fixtures.Core_form.capability_method_call_a_provide_and_a_crash_on_a;
  passes "a value converted to an any value, from an impl and from a bound"
    Fixtures.Core_form.value_converted_to_an_any_value_from_an_impl_and

let () =
  passes "an interpolated string, a tagged string, and a copy"
    Fixtures.Core_form.interpolated_string_a_tagged_string_and_a_copy;
  passes "a set, a map, a record update, a field default, and a parallel block"
    Fixtures.Core_form.set_a_map_a_record_update_a_field_default_and_a

let () =
  passes "an array literal and a generic value parameter used as a value"
    Fixtures.Core_form.array_literal_and_a_generic_value_parameter_used

let () =
  test "a call of a lending method that never yields compiles, and the code after it is unreachable"
    (fun () ->
      expect_output Fixtures.Core_form.call_of_a_lending_method_that_never_yields
        "test 0 panicked\nmessage 35\nno cell\n  at example/main.truss:6:3\n")

let () =
  passes "a loop over a recursive yielding function pulls a cursor over it"
    Fixtures.Core_form.loop_over_a_recursive_yielding_function_pulls_a;
  passes "a pulled yielding function copies the places it yields"
    Fixtures.Core_form.pulled_yielding_function_copies_the_places_it;
  passes "a named function as a value, at its own type and at a wider one"
    Fixtures.Core_form.named_function_as_a_value_at_its_own_type_and_at_a

let () =
  passes "a lambda that captures a local and one that captures self, called through a value"
    Fixtures.Core_form.lambda_that_captures_a_local_and_one_that_captures;
  passes "a method called through an any value"
    Fixtures.Core_form.method_called_through_an_any_value;
  passes "next on a cursor and a loop over the rest of it"
    Fixtures.Core_form.next_on_a_cursor_and_a_loop_over_the_rest_of_it

let () =
  passes "a loop over a value of a type that implements Cursor"
    Fixtures.Core_form.loop_over_a_value_of_a_type_that_implements_cursor

let () =
  passes "a capability method called with arguments left to their defaults"
    Fixtures.Core_form.capability_method_called_with_arguments_left_to

let () =
  passes "a slice of a range of a list, of a slice, and with a bound left out"
    Fixtures.Core_form.slice_of_a_range_of_a_list_of_a_slice_and_with_a

let () =
  passes "a slice of a small array, or of one in a small record, views the caller's array"
    Fixtures.Core_form.slice_of_a_small_array_or_of_one_in_a_small_record

let () =
  passes "constructors of lent places, yielded read-only and `mut`"
    Fixtures.Core_form.constructors_of_lent_places_yielded_read_only_and

let () =
  passes
    "a lent value is read and changed through the addresses it holds, and copied where it is used \
     whole"
    Fixtures.Core_form.lent_value_is_read_and_changed_through_the

let () =
  passes
    "first_value lending method that yields on several paths: places, first_value value it makes, \
     and one built around places"
    Fixtures.Core_form.lending_method_that_yields_on_several_paths_places

let () =
  passes "a method that yields constructors of lent places and loops over itself"
    Fixtures.Core_form.method_that_yields_constructors_of_lent_places_and

let () =
  passes "a value moved out of a `mut` parameter, which is then reinitialized"
    Fixtures.Core_form.value_moved_out_of_a_mut_parameter_which_is_then

let () =
  passes "quantifiers over ranges, which run as loops that stop at the first answer"
    Fixtures.Core_form.quantifiers_over_ranges_which_run_as_loops_that

let () =
  passes "quantifiers over a list, a slice, and a type with an each of its own"
    Fixtures.Core_form.quantifiers_over_a_list_a_slice_and_a_type_with_an

let () =
  passes "constants that are infinite or not a number, which C has no literal for"
    Fixtures.Core_form.constants_that_are_infinite_or_not_a_number_which

let () =
  passes "a yielding function's cursor through a bound, and the methods Cursor gives it"
    Fixtures.Core_form.yielding_functions_cursor_through_a_bound_and_the

let () =
  passes "any of a trait whose methods name an associated type, over two kinds of cursor"
    Fixtures.Core_form.any_of_a_trait_whose_methods_name_an_associated

let () =
  passes "a match that owns a sum takes one variant's payload and drops the other variant whole"
    Fixtures.Core_form.match_that_owns_a_sum_takes_one_variants_payload

let () =
  passes "a loop over a range of characters, which has no surrogates in it"
    Fixtures.Core_form.loop_over_a_range_of_characters_which_has_no

let () =
  passes "a function with a default, called through a function value, uses its arguments"
    Fixtures.Core_form.function_with_a_default_called_through_a_function

(* Checks which of a module's constants fold and which are computed by
   running their evaluators, and that the module's test passes. *)
let folds name ~folded ~run source =
  test name (fun () ->
      let database, _ = load source in
      let context =
        Lower.context ~checks:true database target_64
          ~cursor_fields:(fun _ _ -> failwith "folding a constant lowers no pulled method")
          ~constant:(fun context path ->
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
  folds "constants fold from their core forms, except a set, which is built by running"
    ~folded:[ "small"; "flag"; "names"; "rows"; "corner"; "primes" ]
    ~run:[ "colors" ] Fixtures.Core_form.constants_fold_from_their_core_forms_except_a_set

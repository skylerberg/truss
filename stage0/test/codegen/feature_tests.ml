(* Truss source compiled with the standard library and run: each feature. *)

open Codegen_support

let () =
  passes
    "a derived ordering compares fields in declaration order, and a construction evaluates its \
     fields in the order written"
    Fixtures.Feature.derived_ordering_compares_fields_in_declaration;
  passes "a pulled cursor yields each value and then None"
    Fixtures.Feature.pulled_cursor_yields_each_value_and_then_none;
  passes "a cursor over a method whose receiver has no size keeps its arguments"
    Fixtures.Feature.cursor_over_a_method_whose_receiver_has_no_size;
  (* A cursor that held the evidence it was made with would read the
     [Table]'s list after the first block had dropped it. *)
  passes "a cursor's next uses the implementation provided where it is called"
    Fixtures.Feature.cursors_next_uses_the_implementation_provided;
  test "an associated capability set gives each instance the evidence that its type needs"
    (fun () ->
      expect_output Fixtures.Feature.associated_capability_set_gives_each_instance_the
        (String.concat "" (List.init 8 (Printf.sprintf "test %d passed\n"))));
  passes "a lending method resumes after its caller's statement"
    Fixtures.Feature.lending_method_resumes_after_its_callers_statement;
  passes "a lending method lends a local it owns, which lives until the caller's statement ends"
    Fixtures.Feature.lending_method_lends_a_local_it_owns_which_lives;
  (* The caller continues from either [yield], and only the first has
     [label] in scope. *)
  passes "a lending method owns a value at one of its yields and not at another"
    Fixtures.Feature.lending_method_owns_a_value_at_one_of_its_yields;
  passes "a lending method yields inside a loop over a yielding method that owns a value"
    Fixtures.Feature.lending_method_yields_inside_a_loop_over_a;
  passes "a `lends mut` method yields on two paths, and owns a local at one of them"
    Fixtures.Feature.lends_mut_method_yields_on_two_paths_and_owns_a;
  passes "a lending method resumes when its caller's statement exits early"
    Fixtures.Feature.lending_method_resumes_when_its_callers_statement;
  passes "a cursor dropped before it ends drops its values"
    Fixtures.Feature.cursor_dropped_before_it_ends_drops_its_values;
  passes "sets and maps keep one of each key, in order"
    Fixtures.Feature.sets_and_maps_keep_one_of_each_key_in_order;
  passes "strings, constants, and ranges of constants are patterns"
    Fixtures.Feature.strings_constants_and_ranges_of_constants_are;
  passes "floats display as the shortest decimal that reads back"
    Fixtures.Feature.floats_display_as_the_shortest_decimal_that_reads;
  passes "a range is a value with its ends" Fixtures.Feature.range_is_a_value_with_its_ends;
  passes "a loop that binds an owned value each time frees each one once"
    Fixtures.Feature.loop_that_binds_an_owned_value_each_time_frees;
  passes "provide runs its body with the implementations given, nested and narrowed"
    Fixtures.Feature.provide_runs_its_body_with_the_implementations;
  passes "tagged characters are numbers, in values, constants, and patterns"
    Fixtures.Feature.tagged_characters_are_numbers_in_values_constants;
  passes "a tagged string gives its tag a template of its text and parts"
    Fixtures.Feature.tagged_string_gives_its_tag_a_template_of_its_text;
  passes "a method that yields through recursion drives a for loop"
    Fixtures.Feature.method_that_yields_through_recursion_drives_a_for;
  passes "a recursive loop over views of strings gives copies, and leaves the tree whole"
    Fixtures.Feature.recursive_loop_over_views_of_strings_gives_copies;
  passes "a constant that needs its code run is evaluated while compiling"
    Fixtures.Feature.constant_that_needs_its_code_run_is_evaluated;
  passes "a program of many features together: generics, any, lambdas, ?, Map, mut loops"
    Fixtures.Feature.program_of_many_features_together_generics_any;
  passes "a yielding method's defaults are filled when it is pulled or looped over"
    Fixtures.Feature.yielding_methods_defaults_are_filled_when_it_is;
  passes "a read-only parameter's default with something to drop is dropped once"
    Fixtures.Feature.read_only_parameters_default_with_something_to;
  passes "names an is test binds are used where it holds"
    Fixtures.Feature.names_an_is_test_binds_are_used_where_it_holds;
  passes "a guard that fails leaves the value for the next arm"
    Fixtures.Feature.guard_that_fails_leaves_the_value_for_the_next_arm;
  passes "an expression a pattern looks into is evaluated once"
    Fixtures.Feature.expression_a_pattern_looks_into_is_evaluated_once

let () =
  passes "a list grows as it is pushed and keeps its elements"
    Fixtures.Feature.list_grows_as_it_is_pushed_and_keeps_its_elements;
  passes "text that started as a literal is copied before it is added to"
    Fixtures.Feature.text_that_started_as_a_literal_is_copied_before_it

let () =
  test "values echo as Truss writes them" (fun () ->
      expect_output Fixtures.Feature.values_echo_as_truss_writes_them
        "test 0 passed\n\
         echo 265\n\
         example/main.truss:4:11: Some(true)\n\
         example/main.truss:5:11: Some(1.5)\n\
         example/main.truss:6:11: [1, 2, 3]\n\
         example/main.truss:7:11: \"hi\\n \\${x} \\u{1}\"\n\
         example/main.truss:8:11: Point(x: 0.1, y: 2.0)\n\
         example/main.truss:9:11: -7\n\
         example/main.truss:10:11: Character\"\195\169\"\n\n")

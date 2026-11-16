let () =
  Codegen_support.passes
    "a derived ordering compares fields in declaration order, and a construction evaluates its \
     fields in the order written"
    Fixtures.Feature.entry_ordering_with_counted_reads;
  Codegen_support.test
    "derived methods satisfy the laws of their traits, and a sum type orders by variant" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.derived_light_and_record_methods
        (String.concat "" (List.init 3 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.passes "an assignment through an index inserts a map's key or replaces its value"
    Fixtures.Feature.map_assignment_test;
  Codegen_support.passes "a cursor gives each value and then None" Fixtures.Feature.count_to_cursor;
  Codegen_support.passes "a cursor's next uses the implementation provided where it is called"
    Fixtures.Feature.meter_cursor_under_provide;
  Codegen_support.test
    "an associated capability set gives each instance the evidence that its type needs" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.meters_through_associated_capability_sets
        (String.concat "" (List.init 8 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test "a lending method that calls itself lends a part of its receiver" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.tree_lending_a_part_recursively
        (String.concat "" (List.init 5 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test
    "a lending method that calls itself lends a value that the innermost call made" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.tree_lending_a_made_name_recursively
        (String.concat "" (List.init 2 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test
    "a lent constructor owns the fields that the method made, beside the places it lends" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.shelf_lending_tagged_books
        (String.concat "" (List.init 3 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test
    "a constructor lent `mut` writes each place back when the lend ends, at any depth" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.entry_pair_lent_mut_at_depth
        (String.concat "" (List.init 2 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test "a lending method forwards a part of another lending method's part"
    (fun () ->
      Codegen_support.expect_output Fixtures.Feature.catalog_forwarding_a_lent_part
        (String.concat "" (List.init 3 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.test "a lending method is called through an `any` value" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.titled_through_any
        (String.concat "" (List.init 2 (Printf.sprintf "test %d passed\n"))));
  Codegen_support.passes
    "a lending method lends a local it owns, which lives until the caller's statement ends"
    Fixtures.Feature.holder_lending_an_owned_label;
  Codegen_support.passes "a lending method owns a value on one of its paths and not on another"
    Fixtures.Feature.pair_chosen;
  Codegen_support.passes
    "a lending method lends from a `return` inside a loop, while it owns a value"
    Fixtures.Feature.bag_first_matching;
  Codegen_support.passes "a `lends mut` method lends on two paths, and owns a local on one of them"
    Fixtures.Feature.slots_slot;
  Codegen_support.passes
    "a name that a `while` condition binds from a lent value lives until the body ends"
    Fixtures.Feature.while_condition_binding_a_lent_label;
  Codegen_support.passes "sets and maps keep one of each key, in order"
    Fixtures.Feature.set_and_map_test;
  Codegen_support.passes "strings, constants, and ranges of constants are patterns"
    Fixtures.Feature.command_patterns;
  Codegen_support.passes "floats display as the shortest decimal that reads back"
    Fixtures.Feature.float_display_test;
  Codegen_support.passes "a range is a value with its ends" Fixtures.Feature.range_width;
  Codegen_support.passes "a loop that binds an owned value each time frees each one once"
    Fixtures.Feature.pop_loop_test;
  Codegen_support.passes "provide runs its body with the implementations given, nested and narrowed"
    Fixtures.Feature.nested_and_narrowed_provides;
  Codegen_support.passes "tagged characters are numbers, in values, constants, and patterns"
    Fixtures.Feature.tagged_characters;
  Codegen_support.passes "a tagged string gives its tag a template of its text and parts"
    Fixtures.Feature.sum_template;
  Codegen_support.passes "a constant that needs its code run is evaluated while compiling"
    Fixtures.Feature.constants_computed_while_compiling;
  Codegen_support.passes
    "a program of many features together: generics, any, lambdas, ?, Map, mut loops"
    Fixtures.Feature.many_features_together;
  Codegen_support.passes "a read-only parameter's default with something to drop is dropped once"
    Fixtures.Feature.total_with_a_list_default;
  Codegen_support.passes "names an is test binds are used where it holds"
    Fixtures.Feature.describe_with_is_tests;
  Codegen_support.passes "a guard that fails leaves the value for the next arm"
    Fixtures.Feature.classify_with_a_guard;
  Codegen_support.passes "an expression a pattern looks into is evaluated once"
    Fixtures.Feature.match_on_a_counted_index;
  Codegen_support.passes "a slice of a temporary evaluates the temporary once"
    Fixtures.Feature.slice_of_a_counted_temporary

let () =
  Codegen_support.passes "a list grows as it is pushed and keeps its elements"
    Fixtures.Feature.list_grown_to_a_thousand;
  Codegen_support.passes "a var bound to a string literal holds a copy"
    Fixtures.Feature.var_of_a_string_literal_pushed

let () =
  Codegen_support.test "values echo as Truss writes them" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.value_echoes
        "test 0 passed\n\
         echo 265\n\
         example/main.truss:4:11: Some(true)\n\
         example/main.truss:5:11: Some(1.5)\n\
         example/main.truss:6:11: [1, 2, 3]\n\
         example/main.truss:7:11: \"hi\\n \\${x} \\u{1}\"\n\
         example/main.truss:8:11: Point(x: 0.1, y: 2.0)\n\
         example/main.truss:9:11: -7\n\
         example/main.truss:10:11: Character\"\195\169\"\n\n");
  Codegen_support.test "signed integers narrower than Int64 echo as their values" (fun () ->
      Codegen_support.expect_output Fixtures.Feature.narrow_signed_integer_echoes
        "test 0 passed\n\
         echo 86\n\
         example/main.truss:5:11: -8\n\
         example/main.truss:6:11: -16\n\
         example/main.truss:7:11: -32\n\n")

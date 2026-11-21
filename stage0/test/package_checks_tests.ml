let check packages =
  Database.For_testing.list_diagnostics Database.For_testing.fragment_checkers
    (Support.make_database packages)

let expect_one_diagnostic = Support.expect_one_diagnostic ~check
let expect_fine text = Support.expect_no_diagnostics ~check [ ("app.main", text) ]

let () =
  Harness.test "an impl must live with its trait, its type, or a type its trait names" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.impl_display_for_int64 "package.impl_location");
  Harness.test "only the built-in integer and float types implement the sealed number traits"
    (fun () ->
      List.iter
        (fun (text, says) ->
          let diagnostics =
            check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main")
          in
          if
            not
              (List.exists
                 (fun (diagnostic : Diagnostic.t) ->
                   Diagnostic.Code.name diagnostic.code = "package.sealed_trait_impl"
                   && List.for_all (fun affix -> String.includes ~affix diagnostic.message) says)
                 diagnostics)
          then Harness.fail "found [%s]" (String.concat "; " (Support.list_codes diagnostics)))
        [
          ( Fixtures.Package_checks.signed_integer_impl_for_count,
            [ "the built-in integer types"; "proven for each of them" ] );
          ( Fixtures.Package_checks.floating_point_impl_for_meters,
            [ "the built-in float types"; "the IEEE 754 formats" ] );
        ]);
  Harness.test "an impl may live with a type its trait's arguments name" (fun () ->
      expect_fine Fixtures.Package_checks.impl_from_user_id_for_int64);
  Harness.test "two impls of a trait for one type constructor overlap when their arguments unify"
    (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Package_checks.two_add_impls_for_vector) ]
      in
      if
        not
          (List.mem "package.overlapping_impls"
             (Support.list_codes (check packages (Support.parse_file "app.main"))))
      then Harness.fail "no overlap");
  Harness.test "a type's own method cannot share a name with a trait's" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.own_method_named_like_a_trait_method
        "package.method_name_clash");
  Harness.test "a type's own method may be another overload of a trait's" (fun () ->
      expect_fine Fixtures.Package_checks.own_method_overloading_a_trait_method);
  Harness.test "an impl that writes a method may make it another overload of the type's own"
    (fun () -> expect_fine Fixtures.Package_checks.impl_writing_a_label_overload);
  Harness.test "a method an impl leaves to its trait cannot be an overload of the type's own"
    (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.impl_inheriting_a_label_overload
        "package.method_name_clash");
  Harness.test "an impl cannot give a `String` a method that its view has in the same mode"
    (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.impl_giving_a_string_a_method_of_its_view
        "package.method_name_clash" ~says:"the `to_string` of its view `StringSlice`");
  Harness.test
    "an impl in another package cannot give a `String` another overload of its view's method"
    (fun () ->
      expect_one_diagnostic
        Fixtures.Package_checks.impl_giving_a_string_an_overload_of_a_method_of_its_view
        "package.method_name_clash" ~says:"only an `impl` in its own package");
  Harness.test "an impl cannot give an `Array` a method that its view has in the same mode"
    (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.impl_giving_an_array_a_method_of_its_view
        "package.method_name_clash" ~says:"the `contains` of its view `Slice[Element]`");
  Harness.test "an impl may give a `String` a method that neither it nor its view has" (fun () ->
      expect_fine Fixtures.Package_checks.impl_giving_a_string_a_method_that_its_view_lacks);
  Harness.test
    "an impl in another package may give a `String` a method that its view has as `internal`"
    (fun () ->
      expect_fine
        Fixtures.Package_checks.impl_giving_a_string_a_method_that_its_view_has_as_internal);
  Harness.test "a type's constant cannot share a name with a trait's method" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.constant_named_like_a_trait_method
        "package.method_name_clash");
  Harness.test "a type that contains itself in place needs indirect, with a fix that adds it"
    (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.tree_with_direct_children
        "package.needs_indirect" ~fixed:Fixtures.Package_checks.tree_with_direct_children_fixed);
  Harness.test "a type that contains itself through a collection needs no indirect" (fun () ->
      expect_fine Fixtures.Package_checks.expression_with_a_list_of_arguments);
  Harness.test "a record cannot contain itself through an Option" (fun () ->
      expect_one_diagnostic "type Node(next: Option[Node])\n" "package.needs_indirect");
  Harness.test "constants whose values read each other are an error at each of them" (fun () ->
      let packages =
        Support.setup
          [ ("app.main", "let first: Int64 = second + 1\nlet second: Int64 = first + 1\n") ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "package.constant_cycle"; "package.constant_cycle" ] -> ()
      | found -> Harness.fail "found [%s]" (String.concat "; " found));
  Harness.test "a constant whose value reads itself is an error" (fun () ->
      expect_one_diagnostic "let count: Int64 = count + 1\n" "package.constant_cycle"
        ~says:"in its own value");
  Harness.test "a constant built with a field default that reads the constant is an error"
    (fun () ->
      expect_one_diagnostic
        "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1)\n"
        "package.constant_cycle" ~says:"leaves out the field `y`, whose default reads");
  Harness.test "a constant that sets the field whose default reads the constant is fine" (fun () ->
      expect_fine
        "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1, y: 2)\n");
  Harness.test "a type that contains itself with growing arguments is an error" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.nested_type_with_growing_arguments
        "package.growing_type");
  Harness.test
    "an impl whose associated type grows the type that holds it reaches the recursion limit"
    (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.impl_growing_a_type_through_its_associated_type
        "types.recursion_limit" ~says:"needs more than 64 nested types");
  Harness.test "generic code that instantiates itself with growing arguments is an error" (fun () ->
      let packages =
        Support.setup
          [ ("app.main", Fixtures.Package_checks.function_calling_itself_with_a_growing_type) ]
      in
      if
        not
          (List.mem "package.instantiation_cycle"
             (Support.list_codes (check packages (Support.parse_file "app.main"))))
      then Harness.fail "no cycle");
  Harness.test
    "of generic functions that instantiate each other, only the one whose call grows is an error"
    (fun () ->
      let packages =
        Support.setup
          [
            ( "app.main",
              "fn ping[Element](value: own Element) -> Int64 {\n\
              \  pong(Some(own value))\n\
               }\n\n\
               fn pong[Element](value: own Element) -> Int64 {\n\
              \  ping(own value)\n\
               }\n" );
          ]
      in
      match
        List.filter
          (String.equal "package.instantiation_cycle")
          (Support.list_codes (check packages (Support.parse_file "app.main")))
      with
      | [ _ ] -> ()
      | reported -> Harness.fail "found %d instantiation cycles" (List.length reported));
  Harness.test "generic code that calls through many diamonds is checked quickly" (fun () ->
      let levels = 24 in
      let text =
        String.concat ""
          ("fn start[Element](value: own Element) {\n  g0(Some(own value))\n}\n\n"
           :: List.init levels (fun index ->
               Printf.sprintf
                 "fn g%d[Element](value: Element) {\n\
                 \  a%d(value)\n\
                 \  b%d(value)\n\
                  }\n\n\
                  fn a%d[Element](value: Element) {\n\
                 \  g%d(value)\n\
                  }\n\n\
                  fn b%d[Element](value: Element) {\n\
                 \  g%d(value)\n\
                  }\n\n"
                 index index index index (index + 1) index (index + 1))
          @ [ Printf.sprintf "fn g%d[Element](value: Element) {}\n" levels ])
      in
      let started = Sys.time () in
      expect_fine text;
      if Sys.time () -. started > 5.0 then Harness.fail "took %.1f seconds" (Sys.time () -. started));
  Harness.test "two tests of a package cannot share a name" (fun () ->
      let packages =
        Support.setup
          [ ("app.main", "test \"adds\" {\n}\n"); ("app.other", "test \"adds\" {\n}\n") ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.other")) with
      | [ "package.duplicate_test" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  Harness.test "a long chain of types that hold each other is fine" (fun () ->
      expect_fine
        (String.concat ""
           (List.init 20 (fun index ->
                if index = 19 then "type T19(value: Int64)\n"
                else Printf.sprintf "type T%d(inner: T%d)\n\n" index (index + 1)))));
  Harness.test "nested instances of a generic type are not growing" (fun () ->
      expect_fine Fixtures.Package_checks.nested_couples);
  Harness.test "many types that each hold the next several times are checked quickly" (fun () ->
      let text =
        String.concat ""
          (List.init 16 (fun index ->
               if index = 15 then "type D15(value: Int64)\n"
               else
                 Printf.sprintf "type D%d(a: D%d, b: D%d, c: D%d, d: D%d)\n\n" index (index + 1)
                   (index + 1) (index + 1) (index + 1)))
      in
      let started = Sys.time () in
      expect_fine text;
      if Sys.time () -. started > 5.0 then Harness.fail "took %.1f seconds" (Sys.time () -. started));
  Harness.test "a type held in place through a generic type's argument needs indirect" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.tree_in_a_couple "package.needs_indirect");
  Harness.test "a type held in place through an associated type needs indirect" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.tree_through_an_associated_type
        "package.needs_indirect");
  Harness.test "a type held through a generic type's collection needs no indirect" (fun () ->
      expect_fine Fixtures.Package_checks.tree_in_a_wrapper_list);
  Harness.test "generic types whose arguments grow through each other are both growing" (fun () ->
      let packages =
        Support.setup [ ("app.main", Fixtures.Package_checks.types_growing_through_each_other) ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "package.growing_type"; "package.growing_type" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a generic type that swaps its arguments is not growing" (fun () ->
      expect_fine Fixtures.Package_checks.type_swapping_its_arguments)

let shown = Fixtures.Package_checks.shown
let holder = "type Kept[Source: Shown](part: Source.Part)\n\n"

let () =
  let list_actual text =
    Support.list_codes
      (check (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main"))
  in
  let expect expected text =
    match list_actual text with
    | actual when actual = expected -> ()
    | actual -> Harness.fail "found [%s]" (String.concat "; " actual)
  in
  Harness.test "a type cannot occur in the input of a function type that terminates" (fun () ->
      expect_one_diagnostic "type Knot(run: fn(Knot) -> Bool)\n" "package.not_strictly_positive");
  Harness.test "a type may occur in the input of a function type that uses RunForever" (fun () ->
      expect_fine "type Button(label: String, on_click: (fn(Button) uses RunForever))\n");
  Harness.test "a type may occur in the output of a function type that terminates" (fun () ->
      expect_fine "type Lazy(next: fn() -> Lazy)\n");
  Harness.test "a type cannot occur in such an input inside a collection" (fun () ->
      expect_one_diagnostic "type Knot(runs: List[fn(Knot) -> Bool])\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input inside a type without fields" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.knot_in_a_pending_function_input
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input inside another function type's output"
    (fun () ->
      expect_one_diagnostic "type Knot(make: fn() -> fn(Knot) -> Bool)\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in the input of a function type in such an input" (fun () ->
      expect_one_diagnostic "type Knot(run: fn(fn(Knot) -> Bool) -> Bool)\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input of an any type's associated type" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.knot_in_an_any_types_function_input
        "package.not_strictly_positive");
  Harness.test "a type cannot be the argument that a generic type puts in such an input" (fun () ->
      expect_one_diagnostic Fixtures.Package_checks.callback_of_wrap_in_wrap
        "package.not_strictly_positive");
  Harness.test "a generic type may put another type's argument in such an input" (fun () ->
      expect_fine Fixtures.Package_checks.callback_of_int64_in_a_wrapper);
  Harness.test "each type of a cycle through such an input is an error" (fun () ->
      expect
        [ "package.not_strictly_positive"; "package.not_strictly_positive" ]
        Fixtures.Package_checks.cycle_through_a_function_input);
  Harness.test "a type cannot occur in such an input through an associated type" (fun () ->
      expect_one_diagnostic
        (shown ^ Fixtures.Package_checks.knot_in_an_associated_function_input ^ holder
       ^ "type Knot(held: Kept[Marker])\n")
        "package.not_strictly_positive");
  Harness.test "an associated type cannot put a type in such an input of itself" (fun () ->
      expect_one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_taking_marker_in_a_function_input ^ holder)
        "package.not_strictly_positive");
  Harness.test "an associated type cannot make a type contain itself in place" (fun () ->
      expect_one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_holding_marker_in_place ^ holder)
        "package.needs_indirect");
  Harness.test "an associated type may make a type contain itself in a collection" (fun () ->
      expect_fine (shown ^ Fixtures.Package_checks.associated_type_holding_marker_in_a_list ^ holder));
  Harness.test "only the impl that makes a type contain itself is an error" (fun () ->
      expect_one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_taking_marker_in_a_function_input ^ holder
       ^ Fixtures.Package_checks.outer_holding_kept_marker)
        "package.not_strictly_positive");
  Harness.test
    "an associated type may put the associated type of its impl's parameter in such an input"
    (fun () ->
      expect_fine
        (shown ^ holder ^ Fixtures.Package_checks.function_input_of_a_parameters_associated_type));
  Harness.test "an associated type cannot make a type contain itself through another impl's type"
    (fun () ->
      expect_one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_types_holding_marker_through_an_impls_type)
        "package.not_strictly_positive");
  Harness.test
    "the arguments of an impl's type are generic parameters, as the recursive type check assumes"
    (fun () ->
      expect_one_diagnostic
        (shown ^ holder ^ Fixtures.Package_checks.impl_for_a_box_of_marker)
        "resolve.shadowed_name");
  Harness.test
    "an associated type cannot make a type contain itself through another impl's definition"
    (fun () ->
      expect_one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_types_holding_marker_through_an_impls_definition)
        "package.not_strictly_positive")

let () =
  Harness.test "an impl overlaps an impl in a package it depends on" (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib.vector", Fixtures.Package_checks.vector_adding_elements);
            ("app.main", Fixtures.Package_checks.impl_adding_meters_to_vectors);
          ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "package.overlapping_impls" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "an impl in another package cannot give a type another overload of its method"
    (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib.counter", Fixtures.Package_checks.counter_with_a_label_method);
            ("app.main", Fixtures.Package_checks.impl_overloading_counters_label);
          ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [ "package.method_name_clash" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "an impl in another package may name a method after the type's `internal` method"
    (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "tools") ]
          [
            ("tools.kits", Fixtures.Package_checks.kit_with_an_internal_part);
            ( "app.main",
              Fixtures.Package_checks.impl_naming_a_method_after_an_internal_one_of_another_package
            );
          ]
      in
      match Support.list_codes (check packages (Support.parse_file "app.main")) with
      | [] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "an impl in the type's package counts the type's private method of another module"
    (fun () ->
      expect_one_diagnostic
        ~others:[ ("app.shapes", Fixtures.Package_checks.shape_with_a_private_measure) ]
        Fixtures.Package_checks.impl_naming_a_method_after_a_private_one_of_another_module
        "package.method_name_clash" ~says:"a `measure` of its own");
  Harness.test "impls whose heads unify only through an infinite type do not overlap" (fun () ->
      expect_fine Fixtures.Package_checks.impls_unifying_only_through_an_infinite_type)

let check_package packages = Database.list_file_diagnostics (Support.make_database packages)
let expect_unused = Support.expect_one_diagnostic ~check:check_package

let expect_severity text (severity : Diagnostic.severity) =
  match check_package (Support.setup [ ("app.main", text) ]) (Support.parse_file "app.main") with
  | [ diagnostic ] ->
      if diagnostic.severity <> severity then
        Harness.fail "the unused definition has the other severity"
  | found -> Harness.fail "found [%s]" (String.concat "; " (Support.list_codes found))

let expect_used ?(others = []) ?(file = "app.main") text =
  Support.expect_no_diagnostics ~check:check_package ((file, text) :: others)

let () =
  Harness.test "an internal function that nothing in its package uses is an error" (fun () ->
      expect_unused Fixtures.Package_checks.unused_internal_function "usage.unused_function"
        ~says:"Nothing in `app` uses the internal function `app.main.double`";
      expect_severity Fixtures.Package_checks.unused_internal_function Error);
  Harness.test "an internal constant that nothing in its package uses is rejected" (fun () ->
      expect_unused Fixtures.Package_checks.unused_internal_constant "usage.unused_constant");
  Harness.test "an internal function that only calls itself is rejected" (fun () ->
      expect_unused Fixtures.Package_checks.internal_function_used_only_by_itself
        "usage.unused_function" ~says:"Nothing in `app` uses");
  Harness.test "internal functions that only unused definitions call are rejected together"
    (fun () ->
      let packages =
        Support.setup
          [ ("app.main", Fixtures.Package_checks.internal_functions_used_only_by_each_other) ]
      in
      match check_package packages (Support.parse_file "app.main") with
      | [ first; second ] ->
          let messages = List.sort compare [ first.message; second.message ] in
          if
            messages
            <> [
                 "Nothing in `app` uses the internal function `app.main.quadruple`. Delete it.";
                 "Only unused definitions use the internal function `app.main.twice`. Delete it \
                  with them.";
               ]
          then Harness.fail "found %s" (String.concat "; " messages)
      | found -> Harness.fail "found [%s]" (String.concat "; " (Support.list_codes found)));
  Harness.test "an internal function that another module of the package calls is used" (fun () ->
      expect_used Fixtures.Package_checks.public_function_calling_an_internal_helper
        ~others:[ ("app.helpers", Fixtures.Package_checks.internal_helpers) ]);
  Harness.test "an internal method called with a dot is used" (fun () ->
      expect_used Fixtures.Package_checks.internal_method_called_with_a_dot);
  Harness.test "a method of an internal trait called through the trait is used" (fun () ->
      expect_used Fixtures.Package_checks.internal_trait_method_called_with_a_dot);
  Harness.test "an internal function returned as a value is used" (fun () ->
      expect_used Fixtures.Package_checks.internal_function_returned_as_a_value);
  Harness.test "an internal function named only in an `ensures` is used" (fun () ->
      expect_used Fixtures.Package_checks.internal_function_named_only_in_an_ensures);
  Harness.test "an internal constant named only in a pattern is used" (fun () ->
      expect_used Fixtures.Package_checks.internal_constant_named_only_in_a_pattern
        ~others:[ ("app.limits", Fixtures.Package_checks.internal_limit) ]);
  Harness.test "a private function that nothing in its package uses is a warning" (fun () ->
      expect_unused Fixtures.Package_checks.unused_private_function "usage.unused_function"
        ~says:"Nothing in `app` uses the private function `app.main.double`";
      expect_severity Fixtures.Package_checks.unused_private_function Warning);
  Harness.test "a private function that a test calls is used" (fun () ->
      expect_used Fixtures.Package_checks.private_function_called_by_a_test);
  Harness.test "the `main` of a package's root module is used" (fun () ->
      expect_used ~file:"app" Fixtures.Package_checks.entry_point_alone)

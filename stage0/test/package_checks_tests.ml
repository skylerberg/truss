let check packages = Support.diagnostics (Support.database packages)
let one_diagnostic = Support.one_diagnostic ~check
let fine text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  Harness.test "an impl must live with its trait, its type, or a type its trait names" (fun () ->
      one_diagnostic Fixtures.Package_checks.impl_display_for_int64 "package.impl_location");
  Harness.test "only the built-in integer types implement the integer traits" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Package_checks.signed_integer_impl_for_count) ]
      in
      let found = Support.codes (check packages (Support.file_of "app::main")) in
      if not (List.mem "package.sealed_trait_impl" found) then
        Harness.fail "found [%s]" (String.concat "; " found));
  Harness.test "an impl may live with a type its trait's arguments name" (fun () ->
      fine Fixtures.Package_checks.impl_from_user_id_for_int64);
  Harness.test "two impls of a trait for one type constructor overlap when their arguments unify"
    (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Package_checks.two_add_impls_for_vector) ]
      in
      if
        not
          (List.mem "package.overlapping_impls"
             (Support.codes (check packages (Support.file_of "app::main"))))
      then Harness.fail "no overlap");
  Harness.test "a type's own method cannot share a name with a trait's" (fun () ->
      one_diagnostic Fixtures.Package_checks.own_method_named_like_a_trait_method
        "package.method_name_clash");
  Harness.test "a type's own method may be another overload of a trait's" (fun () ->
      fine Fixtures.Package_checks.own_method_overloading_a_trait_method);
  Harness.test "an impl that writes a method may make it another overload of the type's own"
    (fun () -> fine Fixtures.Package_checks.impl_writing_a_label_overload);
  Harness.test "a method an impl leaves to its trait cannot be an overload of the type's own"
    (fun () ->
      one_diagnostic Fixtures.Package_checks.impl_inheriting_a_label_overload
        "package.method_name_clash");
  Harness.test "a type's constant cannot share a name with a trait's method" (fun () ->
      one_diagnostic Fixtures.Package_checks.constant_named_like_a_trait_method
        "package.method_name_clash");
  Harness.test "a type that contains itself in place needs indirect, with a fix that adds it"
    (fun () ->
      one_diagnostic Fixtures.Package_checks.tree_with_direct_children "package.needs_indirect"
        ~fixed:Fixtures.Package_checks.tree_with_direct_children_fixed);
  Harness.test "a type that contains itself through a collection needs no indirect" (fun () ->
      fine Fixtures.Package_checks.expression_with_a_list_of_arguments);
  Harness.test "a record cannot contain itself through an Option" (fun () ->
      one_diagnostic "type Node(next: Option[Node])\n" "package.needs_indirect");
  Harness.test "constants whose values read each other are an error at each of them" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", "let first: Int64 = second + 1\nlet second: Int64 = first + 1\n") ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.constant_cycle"; "package.constant_cycle" ] -> ()
      | found -> Harness.fail "found [%s]" (String.concat "; " found));
  Harness.test "a constant whose value reads itself is an error" (fun () ->
      one_diagnostic "let count: Int64 = count + 1\n" "package.constant_cycle"
        ~says:"in its own value");
  Harness.test "a constant built with a field default that reads the constant is an error"
    (fun () ->
      one_diagnostic "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1)\n"
        "package.constant_cycle" ~says:"leaves out the field `y`, whose default reads");
  Harness.test "a constant that sets the field whose default reads the constant is fine" (fun () ->
      fine "type Point(x: Int64, y: Int64 = origin.x)\nlet origin: Point = Point(x: 1, y: 2)\n");
  Harness.test "a type that contains itself with growing arguments is an error" (fun () ->
      one_diagnostic Fixtures.Package_checks.nested_type_with_growing_arguments
        "package.growing_type");
  Harness.test "generic code that instantiates itself with growing arguments is an error" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", Fixtures.Package_checks.function_calling_itself_with_a_growing_type) ]
      in
      if
        not
          (List.mem "package.instantiation_cycle"
             (Support.codes (check packages (Support.file_of "app::main"))))
      then Harness.fail "no cycle");
  Harness.test
    "of generic functions that instantiate each other, only the one whose call grows is an error"
    (fun () ->
      let packages =
        Support.setup
          [
            ( "app::main",
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
          (Support.codes (check packages (Support.file_of "app::main")))
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
      fine text;
      if Sys.time () -. started > 5.0 then Harness.fail "took %.1f seconds" (Sys.time () -. started));
  Harness.test "two tests of a package cannot share a name" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", "test \"adds\" {\n}\n"); ("app::other", "test \"adds\" {\n}\n") ]
      in
      match Support.codes (check packages (Support.file_of "app::other")) with
      | [ "package.duplicate_test" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  Harness.test "a long chain of types that hold each other is fine" (fun () ->
      fine
        (String.concat ""
           (List.init 20 (fun index ->
                if index = 19 then "type T19(value: Int64)\n"
                else Printf.sprintf "type T%d(inner: T%d)\n\n" index (index + 1)))));
  Harness.test "nested instances of a generic type are not growing" (fun () ->
      fine Fixtures.Package_checks.nested_couples);
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
      fine text;
      if Sys.time () -. started > 5.0 then Harness.fail "took %.1f seconds" (Sys.time () -. started));
  Harness.test "a type held in place through a generic type's argument needs indirect" (fun () ->
      one_diagnostic Fixtures.Package_checks.tree_in_a_couple "package.needs_indirect");
  Harness.test "a type held in place through an associated type needs indirect" (fun () ->
      one_diagnostic Fixtures.Package_checks.tree_through_an_associated_type
        "package.needs_indirect");
  Harness.test "a type held through a generic type's collection needs no indirect" (fun () ->
      fine Fixtures.Package_checks.tree_in_a_wrapper_list);
  Harness.test "generic types whose arguments grow through each other are both growing" (fun () ->
      let packages =
        Support.setup [ ("app::main", Fixtures.Package_checks.types_growing_through_each_other) ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.growing_type"; "package.growing_type" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a generic type that swaps its arguments is not growing" (fun () ->
      fine Fixtures.Package_checks.type_swapping_its_arguments)

let shown = Fixtures.Package_checks.shown
let holder = "type Kept[Source: Shown](part: Source.Part)\n\n"

let () =
  let actual text =
    Support.codes (check (Support.setup [ ("app::main", text) ]) (Support.file_of "app::main"))
  in
  let expect expected text =
    match actual text with
    | actual when actual = expected -> ()
    | actual -> Harness.fail "found [%s]" (String.concat "; " actual)
  in
  Harness.test "a type cannot occur in the input of a function type that has a time clause"
    (fun () ->
      one_diagnostic "type Knot(run: (fn(Knot) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  Harness.test "a type may occur in the input of a function type that has no time clause" (fun () ->
      fine "type Button(label: String, on_click: fn(Button))\n");
  Harness.test "a type may occur in the output of a function type that has a time clause" (fun () ->
      fine "type Lazy(next: (fn() -> Lazy cost time finite))\n");
  Harness.test "a type cannot occur in such an input inside a collection" (fun () ->
      one_diagnostic "type Knot(runs: List[(fn(Knot) -> Bool cost time finite)])\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input inside a type without fields" (fun () ->
      one_diagnostic Fixtures.Package_checks.knot_in_a_pending_function_input
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input inside another function type's output"
    (fun () ->
      one_diagnostic "type Knot(make: fn() -> (fn(Knot) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in the input of a function type in such an input" (fun () ->
      one_diagnostic "type Knot(run: (fn(fn(Knot) -> Bool) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input of an any type's associated type" (fun () ->
      one_diagnostic Fixtures.Package_checks.knot_in_an_any_types_function_input
        "package.not_strictly_positive");
  Harness.test "a type cannot be the argument that a generic type puts in such an input" (fun () ->
      one_diagnostic Fixtures.Package_checks.callback_of_wrap_in_wrap
        "package.not_strictly_positive");
  Harness.test "a generic type may put another type's argument in such an input" (fun () ->
      fine Fixtures.Package_checks.callback_of_int64_in_a_wrapper);
  Harness.test "each type of a cycle through such an input is an error" (fun () ->
      expect
        [ "package.not_strictly_positive"; "package.not_strictly_positive" ]
        Fixtures.Package_checks.cycle_through_a_function_input);
  Harness.test "a type cannot occur in such an input through an associated type" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.knot_in_an_associated_function_input ^ holder
       ^ "type Knot(held: Kept[Marker])\n")
        "package.not_strictly_positive");
  Harness.test "an associated type cannot put a type in such an input of itself" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_taking_marker_in_a_function_input ^ holder)
        "package.not_strictly_positive");
  Harness.test "an associated type cannot make a type contain itself in place" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_holding_marker_in_place ^ holder)
        "package.needs_indirect");
  Harness.test "an associated type may make a type contain itself in a collection" (fun () ->
      fine (shown ^ Fixtures.Package_checks.associated_type_holding_marker_in_a_list ^ holder));
  Harness.test "only the impl that makes a type contain itself is an error" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_taking_marker_in_a_function_input ^ holder
       ^ Fixtures.Package_checks.outer_holding_kept_marker)
        "package.not_strictly_positive");
  Harness.test
    "an associated type may put the associated type of its impl's parameter in such an input"
    (fun () ->
      fine (shown ^ holder ^ Fixtures.Package_checks.function_input_of_a_parameters_associated_type));
  Harness.test "an associated type cannot make a type contain itself through another impl's type"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_types_holding_marker_through_an_impls_type)
        "package.not_strictly_positive");
  Harness.test
    "the arguments of an impl's type are generic parameters, as the recursive type check assumes"
    (fun () ->
      one_diagnostic
        (shown ^ holder ^ Fixtures.Package_checks.impl_for_a_box_of_marker)
        "resolve.shadowed_name");
  Harness.test
    "an associated type cannot make a type contain itself through another impl's definition"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_types_holding_marker_through_an_impls_definition)
        "package.not_strictly_positive")

let () =
  Harness.test "an impl overlaps an impl in a package it depends on" (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib::vector", Fixtures.Package_checks.vector_adding_elements);
            ("app::main", Fixtures.Package_checks.impl_adding_meters_to_vectors);
          ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.overlapping_impls" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "an impl in another package cannot give a type another overload of its method"
    (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib::counter", Fixtures.Package_checks.counter_with_a_label_method);
            ("app::main", Fixtures.Package_checks.impl_overloading_counters_label);
          ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.method_name_clash" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "impls whose heads unify only through an infinite type do not overlap" (fun () ->
      fine Fixtures.Package_checks.impls_unifying_only_through_an_infinite_type)

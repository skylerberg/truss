let check packages = Support.diagnostics (Support.database packages)
let one_diagnostic = Support.one_diagnostic ~check
let fine text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  Harness.test "an impl must live with its trait, its type, or a type its trait names" (fun () ->
      one_diagnostic Fixtures.Package_checks.impl_must_live_with_its_trait_its_type_or_a_type
        "package.impl_location");
  Harness.test "only the built-in integer types implement the integer traits" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", Fixtures.Package_checks.only_the_built_in_integer_types_implement_the) ]
      in
      let found = Support.codes (check packages (Support.file_of "app::main")) in
      if not (List.mem "package.sealed_trait_impl" found) then
        Harness.fail "found [%s]" (String.concat "; " found));
  Harness.test "an impl may live with a type its trait's arguments name" (fun () ->
      fine Fixtures.Package_checks.impl_may_live_with_a_type_its_traits_arguments);
  Harness.test "two impls of a trait for one type constructor overlap when their arguments unify"
    (fun () ->
      let packages =
        Support.setup
          [ ("app::main", Fixtures.Package_checks.two_impls_of_a_trait_for_one_type_constructor) ]
      in
      if
        not
          (List.mem "package.overlapping_impls"
             (Support.codes (check packages (Support.file_of "app::main"))))
      then Harness.fail "no overlap");
  Harness.test "a type's own method cannot share a name with a trait's" (fun () ->
      one_diagnostic Fixtures.Package_checks.types_own_method_cannot_share_a_name_with_a_traits
        "package.method_name_clash");
  Harness.test "a type's own method may be another overload of a trait's" (fun () ->
      fine Fixtures.Package_checks.types_own_method_may_be_another_version_of_a);
  Harness.test "an impl that writes a method may make it another overload of the type's own"
    (fun () -> fine Fixtures.Package_checks.impl_that_writes_a_method_may_make_it_another);
  Harness.test "a method an impl leaves to its trait cannot be an overload of the type's own"
    (fun () ->
      one_diagnostic Fixtures.Package_checks.method_an_impl_leaves_to_its_trait_cannot_be_a
        "package.method_name_clash");
  Harness.test "a type's constant cannot share a name with a trait's method" (fun () ->
      one_diagnostic Fixtures.Package_checks.types_constant_cannot_share_a_name_with_a_traits
        "package.method_name_clash");
  Harness.test "a type that contains itself in place needs indirect, with a fix that adds it"
    (fun () ->
      one_diagnostic Fixtures.Package_checks.type_that_contains_itself_in_place_needs_indirect
        "package.needs_indirect"
        ~fixed:Fixtures.Package_checks.type_that_contains_itself_in_place_needs_indirect_fixed);
  Harness.test "a type that contains itself through a collection needs no indirect" (fun () ->
      fine Fixtures.Package_checks.type_that_contains_itself_through_a_collection);
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
      one_diagnostic Fixtures.Package_checks.type_that_contains_itself_with_growing_arguments
        "package.growing_type");
  Harness.test "generic code that instantiates itself with growing arguments is an error" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Package_checks.generic_code_that_instantiates_itself_with_growing);
          ]
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
      fine Fixtures.Package_checks.nested_instances_of_a_generic_type_are_not_growing);
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
      one_diagnostic Fixtures.Package_checks.type_held_in_place_through_a_generic_types
        "package.needs_indirect");
  Harness.test "a type held in place through an associated type needs indirect" (fun () ->
      one_diagnostic Fixtures.Package_checks.type_held_in_place_through_an_associated_type
        "package.needs_indirect");
  Harness.test "a type held through a generic type's collection needs no indirect" (fun () ->
      fine Fixtures.Package_checks.type_held_through_a_generic_types_collection_needs);
  Harness.test "generic types whose arguments grow through each other are both growing" (fun () ->
      let packages =
        Support.setup
          [ ("app::main", Fixtures.Package_checks.generic_types_whose_arguments_grow_through_each) ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.growing_type"; "package.growing_type" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a generic type that swaps its arguments is not growing" (fun () ->
      fine Fixtures.Package_checks.generic_type_that_swaps_its_arguments_is_not)

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
      one_diagnostic Fixtures.Package_checks.type_cannot_occur_in_such_an_input_inside_a_type
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input inside another function type's output"
    (fun () ->
      one_diagnostic "type Knot(make: fn() -> (fn(Knot) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in the input of a function type in such an input" (fun () ->
      one_diagnostic "type Knot(run: (fn(fn(Knot) -> Bool) -> Bool cost time finite))\n"
        "package.not_strictly_positive");
  Harness.test "a type cannot occur in such an input of an any type's associated type" (fun () ->
      one_diagnostic Fixtures.Package_checks.type_cannot_occur_in_such_an_input_of_an_any_types
        "package.not_strictly_positive");
  Harness.test "a type cannot be the argument that a generic type puts in such an input" (fun () ->
      one_diagnostic Fixtures.Package_checks.type_cannot_be_the_argument_that_a_generic_type
        "package.not_strictly_positive");
  Harness.test "a generic type may put another type's argument in such an input" (fun () ->
      fine Fixtures.Package_checks.generic_type_may_put_another_types_argument_in);
  Harness.test "each type of a cycle through such an input is an error" (fun () ->
      expect
        [ "package.not_strictly_positive"; "package.not_strictly_positive" ]
        Fixtures.Package_checks.each_type_of_a_cycle_through_such_an_input_is_an);
  Harness.test "a type cannot occur in such an input through an associated type" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.type_cannot_occur_in_such_an_input_through_an ^ holder
       ^ "type Knot(held: Kept[Marker])\n")
        "package.not_strictly_positive");
  Harness.test "an associated type cannot put a type in such an input of itself" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_cannot_put_a_type_in_such_an_input ^ holder)
        "package.not_strictly_positive");
  Harness.test "an associated type cannot make a type contain itself in place" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.associated_type_cannot_make_a_type_contain_itself ^ holder)
        "package.needs_indirect");
  Harness.test "an associated type may make a type contain itself in a collection" (fun () ->
      fine
        (shown ^ Fixtures.Package_checks.associated_type_may_make_a_type_contain_itself_in ^ holder));
  Harness.test "only the impl that makes a type contain itself is an error" (fun () ->
      one_diagnostic
        (shown ^ Fixtures.Package_checks.only_the_impl_that_makes_a_type_contain_itself_is ^ holder
       ^ Fixtures.Package_checks.only_the_impl_that_makes_a_type_contain_itself_is_2)
        "package.not_strictly_positive");
  Harness.test
    "an associated type may put the associated type of its impl's parameter in such an input"
    (fun () ->
      fine
        (shown ^ holder ^ Fixtures.Package_checks.associated_type_may_put_the_associated_type_of_its));
  Harness.test "an associated type cannot make a type contain itself through another impl's type"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_type_cannot_make_a_type_contain_itself_2)
        "package.not_strictly_positive");
  Harness.test
    "the arguments of an impl's type are generic parameters, as the recursive type check assumes"
    (fun () ->
      one_diagnostic
        (shown ^ holder ^ Fixtures.Package_checks.arguments_of_an_impls_type_are_generic_parameters)
        "resolve.shadowed_name");
  Harness.test
    "an associated type cannot make a type contain itself through another impl's definition"
    (fun () ->
      one_diagnostic
        (shown ^ holder
       ^ Fixtures.Package_checks.associated_type_cannot_make_a_type_contain_itself_3)
        "package.not_strictly_positive")

let () =
  Harness.test "an impl overlaps an impl in a package it depends on" (fun () ->
      let packages =
        Support.setup
          ~dependencies:[ ("app", "lib") ]
          [
            ("lib::vector", Fixtures.Package_checks.impl_overlaps_an_impl_in_a_package_it_depends_on);
            ("app::main", Fixtures.Package_checks.impl_overlaps_an_impl_in_a_package_it_depends_on_2);
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
            ( "lib::counter",
              Fixtures.Package_checks.impl_in_another_package_cannot_give_a_type_another );
            ( "app::main",
              Fixtures.Package_checks.impl_in_another_package_cannot_give_a_type_another_2 );
          ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "package.method_name_clash" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "impls whose heads unify only through an infinite type do not overlap" (fun () ->
      fine Fixtures.Package_checks.impls_whose_heads_unify_only_through_an_infinite)

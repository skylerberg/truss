(* The tests of capabilities: capability checking, lambdas' uses,
   capability parameters, provide, and dependency grants. *)

open Harness
open Support

let check = Type_checker.For_testing.through Infer
let one_diagnostic = one_diagnostic ~check
let fine text = no_diagnostics ~check [ ("app::main", text) ]

let () =
  test "a capability call needs its capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.capability_call_needs_its_capability
        "capabilities.not_available");
  test "a function that declares a capability may call it" (fun () ->
      fine Fixtures.Capabilities.function_that_declares_a_capability_may_call_it);
  test "a call to a function with uses needs its capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.call_to_a_function_with_uses_needs_its
        "capabilities.not_available");
  test "provide makes a capability available in its block" (fun () ->
      fine Fixtures.Capabilities.provide_makes_a_capability_available_in_its_block);
  test "provide records each capability's impl with its generic arguments" (fun () ->
      let text = Fixtures.Capabilities.provide_records_each_capabilitys_impl_with_its in
      let database = setup [ ("app::main", text) ] in
      let key : Resolve.Names.key =
        {
          module_ = module_of "app::main";
          path = Top { module_ = module_of "app::main"; name = "run_example" };
          ordinal = 0;
        }
      in
      match
        List.filter_map
          (fun (node : Core.expression) ->
            match node.kind with
            | Provide { implementations; _ } ->
                Some
                  (List.map
                     (fun (implementation : Core.implementation) -> implementation.provides)
                     implementations)
            | _ -> None)
          (core_nodes database key).expressions
      with
      | [ [ [ { capability; impl = Impl _; arguments = [ (_, Type tag) ] } ] ] ]
        when Path.show capability = "standard::capabilities::Clock" && Types.show tag = "Bool" ->
          ()
      | _ -> fail "not recorded");
  test "a specification may not use Panic" (fun () ->
      one_diagnostic Fixtures.Capabilities.specification_may_not_use_panic
        "capabilities.not_available");
  test "a specification cannot use the function's capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.specification_cannot_use_the_functions
        "capabilities.not_available");
  test "a loop invariant cannot use the function's capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.loop_invariant_cannot_use_the_functions
        "capabilities.not_available");
  test "a type's invariant may use no capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.types_invariant_may_use_no_capability
        "capabilities.not_available");
  test "a law may use no capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.law_may_use_no_capability "capabilities.not_available");
  test "a parallel branch has only Panic" (fun () ->
      one_diagnostic Fixtures.Capabilities.parallel_branch_has_only_panic
        "capabilities.not_available");
  test "a lambda's uses must fit the function type it is passed as" (fun () ->
      one_diagnostic Fixtures.Capabilities.lambdas_uses_must_fit_the_function_type_it_is
        "capabilities.lambda_uses");
  test "a loop over a value needs the capabilities that its `each` uses" (fun () ->
      one_diagnostic Fixtures.Capabilities.loop_over_a_value_needs_the_capabilities_that_its
        "capabilities.not_available");
  test "a loop over a value can use the function's capabilities" (fun () ->
      fine Fixtures.Capabilities.loop_over_a_value_can_use_the_functions);
  test "a capability parameter is instantiated with the capabilities of the lambdas passed for it"
    (fun () -> fine Fixtures.Capabilities.capability_parameter_is_instantiated_with_the);
  test "a trait's method solves its capability parameter as a function does" (fun () ->
      let visitor = Fixtures.Capabilities.visitor in
      let call =
        "{\n  numbers.visit_all(fn(value) {\n    let _ = Clock.now()\n    let _ = value\n  })\n}\n"
      in
      fine (visitor ^ "fn run_example(numbers: Numbers)\n  uses Clock\n" ^ call);
      one_diagnostic
        (visitor ^ "fn run_example(numbers: Numbers)\n" ^ call)
        "capabilities.not_available");
  test "a capability parameter's set must be available at the call" (fun () ->
      one_diagnostic Fixtures.Capabilities.capability_parameters_set_must_be_available_at_the
        "capabilities.not_available");
  test "a test has Panic" (fun () -> fine Fixtures.Capabilities.test_has_panic);
  test "a place whose implementation changes state is provided mut" (fun () ->
      one_diagnostic Fixtures.Capabilities.place_whose_implementation_changes_state_is
        "capabilities.provide_mark")

let () =
  test "a dependency can use only the capabilities that it is granted" (fun () ->
      let database =
        setup
          [
            ("app::main", Fixtures.Capabilities.dependency_can_use_only_the_capabilities_that_it);
            ( "clock_library::time",
              Fixtures.Capabilities.dependency_can_use_only_the_capabilities_that_it_time );
          ]
      in
      Database.For_testing.set_manifest (Engine.of_context database)
        ~name:{ owner = None; name = "app" }
        ~dependencies:[ { package = { owner = None; name = "clock_library" }; capabilities = [] } ];
      match codes (check database (module_of "app::main")) with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual))

let () =
  let with_grant files granted =
    let database = setup files in
    Database.For_testing.set_manifest (Engine.of_context database)
      ~name:{ owner = None; name = "app" }
      ~dependencies:
        [ { package = { owner = None; name = "clock_library" }; capabilities = granted } ];
    codes (check database (module_of "app::main"))
  in
  let library = ("clock_library::time", Fixtures.Capabilities.library_time) in
  test "a dependency's trait method can use only the granted capabilities" (fun () ->
      match
        with_grant
          [
            ("app::main", Fixtures.Capabilities.dependencys_trait_method_can_use_only_the_granted);
            library;
          ]
          []
      with
      | "capabilities.not_granted" :: _ -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "a dependency's trait method can use a granted capability" (fun () ->
      match
        with_grant
          [
            ("app::main", Fixtures.Capabilities.dependencys_trait_method_can_use_a_granted); library;
          ]
          [ "Clock" ]
      with
      | [] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual));
  test "providing a dependency's type checks the grants for the capabilities of its impls"
    (fun () ->
      match
        with_grant
          [
            ("app::main", Fixtures.Capabilities.providing_a_dependencys_type_checks_the_grants_for);
            library;
          ]
          []
      with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> fail "found [%s]" (String.concat "; " actual))

let () =
  test "an implementation of a capability may not call the capability directly" (fun () ->
      one_diagnostic Fixtures.Capabilities.implementation_of_a_capability_may_not_call_the
        "capabilities.not_available");
  test "an implementation of a capability may hand the capability to a function value" (fun () ->
      fine Fixtures.Capabilities.implementation_of_a_capability_may_hand_the)

(* A grant wherever a dependency's code is named *)

(* The codes of [app::main], whose manifest lists the dependencies given,
   each with its grants. *)
let codes_with_grants files grants =
  let database = setup files in
  Database.For_testing.set_manifest (Engine.of_context database)
    ~name:{ owner = None; name = "app" }
    ~dependencies:
      (List.map (fun (package, capabilities) -> { Manifest.package; capabilities }) grants);
  (database, codes (check database (module_of "app::main")))

let expect_codes ~expected (_, actual) =
  if actual <> expected then
    fail "found [%s], expected [%s]" (String.concat "; " actual) (String.concat "; " expected)

let time = ("clock_library::time", Fixtures.Capabilities.time_time)
let sources = ("framework::sources", Fixtures.Capabilities.sources_sources)
let timers = ("plugins::timers", Fixtures.Capabilities.timers_timers)

let () =
  let value = ("app::main", Fixtures.Capabilities.value) in
  test "a function value of a dependency's function can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ value; time ] [ ({ owner = None; name = "clock_library" }, []) ]));
  test "a function value of a dependency's function can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ value; time ]
           [ ({ owner = None; name = "clock_library" }, [ "Clock" ]) ]));
  let bound = ("app::main", Fixtures.Capabilities.bound) in
  test "an impl of a dependency that satisfies a bound can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]));
  test "an impl of a dependency that satisfies a bound can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, [ "Clock" ]);
           ]));
  test "an impl of a dependency behind an `any` value can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants
           [
             ("app::main", Fixtures.Capabilities.impl_of_a_dependency_behind_an_any_value_can_use);
             sources;
             timers;
           ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]))

(* Grant names *)

let ledger = ("store::ledger", Fixtures.Capabilities.ledger_ledger)
let pays = ("app::main", Fixtures.Capabilities.pays)

let problems database =
  Query.demand database Type_checker.manifest_problems { owner = None; name = "app" }

let () =
  test "a grant names a capability outside the prelude by its full path" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ pays; ledger ]
           [ ({ owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]));
  test "a capability's name alone grants only one of the prelude" (fun () ->
      let database, actual =
        codes_with_grants [ pays; ledger ] [ ({ owner = None; name = "store" }, [ "Ledger" ]) ]
      in
      expect_codes ~expected:[ "capabilities.not_granted" ] (database, actual);
      match problems database with
      | [ Not_a_capability { dependency = { Path.owner = None; name = "store" }; name = "Ledger" } ]
        ->
          ()
      | _ -> fail "the grant is not reported");
  test "a grant covers only the capabilities it names" (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ pays; ledger ]
           [ ({ Path.owner = None; name = "store" }, [ "Clock" ]) ]))

(* A dependency that nothing uses *)

let () =
  test "a dependency that nothing in the package names is reported" (fun () ->
      let database, _ =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.dependency_that_nothing_in_the_package_names_is);
            time;
          ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      match problems database with
      | [ Unused { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> fail "not reported");
  test "a dependency named in a path is used" (fun () ->
      let database, _ =
        codes_with_grants [ pays; ledger ]
          [ ({ Path.owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]
      in
      if problems database <> [] then fail "reported");
  test "a dependency whose trait's method is called with a dot is used" (fun () ->
      let database, actual =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.dependency_whose_traits_method_is_called_with_a);
            ( "shapes::sizes",
              Fixtures.Capabilities.dependency_whose_traits_method_is_called_with_a_sizes );
          ]
          [ ({ Path.owner = None; name = "shapes" }, []) ]
      in
      expect_codes ~expected:[] (database, actual);
      if problems database <> [] then fail "reported");
  test "an unused dependency is reported for every kind of definition in the package" (fun () ->
      let database, actual =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.unused_dependency_is_reported_for_every_kind_of);
            time;
          ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      expect_codes ~expected:[] (database, actual);
      match problems database with
      | [ Unused { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> fail "not reported");
  test "an unused dependency is not reported for a package with an error" (fun () ->
      let database, _ =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.unused_dependency_is_not_reported_for_a_package);
            time;
          ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      if problems database <> [] then fail "reported")

(* Function values and the capabilities their types list *)

let ticks = Fixtures.Capabilities.ticks

let () =
  test "a function that uses a capability is not passed as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_that_uses_a_capability_is_not_passed_as)
        "types.mismatch");
  test "a function that uses a capability is not bound as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_that_uses_a_capability_is_not_bound_as)
        "types.mismatch");
  test "a function that uses a capability is not returned as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_that_uses_a_capability_is_not_returned_as)
        "types.mismatch");
  test "a function that uses a capability is not stored as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_that_uses_a_capability_is_not_stored_as)
        "types.mismatch");
  test "a function that uses a capability is not assigned as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_that_uses_a_capability_is_not_assigned_as)
        "types.mismatch");
  test "function types inside a type must list the same capabilities" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.function_types_inside_a_type_must_list_the_same)
        "types.mismatch");
  test "a function that uses nothing is passed as one that may use a capability" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.function_that_uses_nothing_is_passed_as_one_that));
  test "a branch's function meets the function type expected of the branches" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.branchs_function_meets_the_function_type_expected));
  test "a branch's function that uses a capability is not bound as one that uses none" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.branchs_function_that_uses_a_capability_is_not)
        "types.mismatch");
  test "a capability parameter is instantiated with the capabilities of the functions passed for it"
    (fun () -> fine (ticks ^ Fixtures.Capabilities.capability_parameter_is_instantiated_with_the_2));
  test "the capabilities of a function passed for a capability parameter must be available"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.capabilities_of_a_function_passed_for_a_capability)
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a parenthesized lambda"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.capability_parameter_is_instantiated_with_the_3)
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a function in a branch"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.capability_parameter_is_instantiated_with_the_4)
        "capabilities.not_available");
  test "a capability parameter is instantiated with the capabilities of a lambda in a branch"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.capability_parameter_is_instantiated_with_the_5)
        "capabilities.not_available");
  test "a function passes its own capability parameter on" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.function_passes_its_own_capability_parameter_on));
  test "a function's own capability parameter is rigid in a lambda's type" (fun () ->
      one_diagnostic Fixtures.Capabilities.functions_own_capability_parameter_is_rigid_in_a
        "capabilities.lambda_uses");
  test "a function's own capability parameter is rigid in a binding's type" (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.functions_own_capability_parameter_is_rigid_in_a_2)
        "types.mismatch");
  test "a function calls itself with its own capability parameter" (fun () ->
      fine Fixtures.Capabilities.function_calls_itself_with_its_own_capability);
  test "a recursive call needs the capabilities that it passes for its capability parameter"
    (fun () ->
      let repeat uses =
        ticks
        ^ "fn repeat[capability Mine](action: (fn() -> Instant uses Mine), again: Bool) -> Instant\n\
          \  uses " ^ uses
        ^ "\n{\n  if again {\n    repeat(tick, again: false)\n  } else {\n    action()\n  }\n}\n"
      in
      one_diagnostic (repeat "Mine") "capabilities.not_available";
      fine (repeat "Mine, Clock"))

(* A capability parameter in a call's arguments, and in a type *)

let later = ticks ^ Fixtures.Capabilities.later

let () =
  test "a call's result has the capabilities that were passed for the capability parameter"
    (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.calls_result_has_the_capabilities_that_were_passed)
        "capabilities.not_available";
      fine (later ^ Fixtures.Capabilities.calls_result_has_the_capabilities_that_were_passed_2);
      fine (later ^ Fixtures.Capabilities.calls_result_has_the_capabilities_that_were_passed_3));
  test "a call's result must fit the function type that it is checked against" (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.calls_result_must_fit_the_function_type_that_it_is)
        "types.mismatch";
      fine (later ^ Fixtures.Capabilities.calls_result_must_fit_the_function_type_that_it_is_2));
  test "a variable that is assigned a second function has the capabilities of both" (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.variable_that_is_assigned_a_second_function_has)
        "capabilities.not_available";
      fine (later ^ Fixtures.Capabilities.variable_that_is_assigned_a_second_function_has_2));
  test "a type and a trait cannot take a capability parameter" (fun () ->
      one_diagnostic "type Holder[capability Granted](action: (fn() -> Instant uses Granted))\n"
        "types.misplaced_capability_parameter";
      one_diagnostic Fixtures.Capabilities.type_and_a_trait_cannot_take_a_capability
        "types.misplaced_capability_parameter";
      fine "type Holder(action: (fn() -> Instant uses Clock))\n")

(* Function values and the costs their types promise *)

(* How many conversions of a function value to a function type with weaker
   costs the first definition of a text has. The prover must show that the
   given costs imply the expected ones at each. *)
let widenings text =
  List.length
    (List.filter
       (fun (node : Core.expression) ->
         match node.kind with Convert { conversion = Widen; _ } -> true | _ -> false)
       (first_core_nodes text).expressions)

let () =
  test "a function bound as a type that promises a cost leaves the cost to the prover" (fun () ->
      match widenings Fixtures.Capabilities.function_bound_as_a_type_that_promises_a_cost with
      | 1 -> ()
      | actual -> fail "%d conversions" actual);
  test "a function that promises to end can be bound as one that does" (fun () ->
      fine Fixtures.Capabilities.function_that_promises_to_end_can_be_bound_as_one);
  test "function types inside a type must promise the same costs" (fun () ->
      one_diagnostic Fixtures.Capabilities.function_types_inside_a_type_must_promise_the_same
        "types.mismatch")

(* The cursor of a yielding method that uses a capability *)

let readings = Fixtures.Capabilities.readings

let () =
  test "the next of a cursor needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.next_of_a_cursor_needs_the_capabilities_of_the)
        "capabilities.not_available");
  test "the next of a cursor is fine where the method's capabilities are available" (fun () ->
      fine (readings ^ Fixtures.Capabilities.next_of_a_cursor_is_fine_where_the_methods));
  test "a for loop over a cursor needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.for_loop_over_a_cursor_needs_the_capabilities_of)
        "capabilities.not_available");
  test "a cursor whose method uses a capability meets a Cursor bound" (fun () ->
      fine (readings ^ Fixtures.Capabilities.cursor_whose_method_uses_a_capability_meets_a));
  test "a generic function that advances a cursor needs the cursor's capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.generic_function_that_advances_a_cursor_needs_the
        "capabilities.not_available");
  test "a call that passes a cursor needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.call_that_passes_a_cursor_needs_the_capabilities)
        "capabilities.not_available");
  test "a method that Cursor provides needs the capabilities of the cursor's method" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.method_that_cursor_provides_needs_the_capabilities)
        "capabilities.not_available");
  test "a method that Cursor provides runs where the cursor's capabilities are available" (fun () ->
      fine (readings ^ Fixtures.Capabilities.method_that_cursor_provides_runs_where_the_cursors));
  test "a cursor whose method uses no capability needs none" (fun () ->
      fine Fixtures.Capabilities.cursor_whose_method_uses_no_capability_needs_none);
  test "a cursor whose method uses a capability cannot be an any value" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.cursor_whose_method_uses_a_capability_cannot_be_an)
        "types.no_impl")

(* Associated capability sets *)

let feed = Fixtures.Capabilities.feed

let () =
  test "an impl that leaves out an associated capability set has the empty set" (fun () ->
      fine (feed ^ Fixtures.Capabilities.impl_that_leaves_out_an_associated_capability_set));
  test "a call needs the capabilities of the set that the impl defines" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.call_needs_the_capabilities_of_the_set_that_the)
        "capabilities.not_available");
  test "a provided method needs the capabilities of the set that the impl defines" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.provided_method_needs_the_capabilities_of_the_set)
        "capabilities.not_available");
  test "a set defined from a parameter's set is the argument's set" (fun () ->
      fine (feed ^ Fixtures.Capabilities.set_defined_from_a_parameters_set_is_the_arguments);
      one_diagnostic
        (feed ^ Fixtures.Capabilities.set_defined_from_a_parameters_set_is_the_arguments_2)
        "capabilities.not_available");
  test "a method of an impl can use only the set that the impl defines" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.method_of_an_impl_can_use_only_the_set_that_the)
        "types.impl_uses");
  test "an impl defines only a set that its trait declares, and only once" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.impl_defines_only_a_set_that_its_trait_declares)
        "types.extra_member";
      one_diagnostic
        (feed ^ Fixtures.Capabilities.impl_defines_only_a_set_that_its_trait_declares_2)
        "types.extra_member");
  test "a set cannot be defined from itself" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.set_cannot_be_defined_from_itself)
        "types.unknown_associated_capability");
  test "an associated capability set is of a trait that declares it" (fun () ->
      one_diagnostic Fixtures.Capabilities.associated_capability_set_is_of_a_trait_that
        "types.unknown_associated_capability";
      one_diagnostic Fixtures.Capabilities.associated_capability_set_is_of_a_trait_that_2
        "types.unknown_associated_capability";
      one_diagnostic Fixtures.Capabilities.associated_capability_set_is_of_a_trait_that_3
        "types.misplaced_self_type";
      one_diagnostic Fixtures.Capabilities.associated_capability_set_is_of_a_trait_that_4
        "resolve.not_a_generic_parameter";
      one_diagnostic Fixtures.Capabilities.associated_capability_set_is_of_a_trait_that_5
        "types.unknown_associated_type");
  test "a trait's methods can use a set that a required trait declares" (fun () ->
      let rewind = Fixtures.Capabilities.rewind in
      fine (feed ^ rewind ^ Fixtures.Capabilities.traits_methods_can_use_a_set_that_a_required_trait);
      one_diagnostic
        (feed ^ rewind ^ Fixtures.Capabilities.traits_methods_can_use_a_set_that_a_required_trait_2)
        "capabilities.not_available");
  test "a function type can use an associated capability set" (fun () ->
      let apply = Fixtures.Capabilities.apply in
      fine (feed ^ apply ^ Fixtures.Capabilities.function_type_can_use_an_associated_capability_set);
      one_diagnostic
        (feed ^ apply ^ Fixtures.Capabilities.function_type_can_use_an_associated_capability_set_2)
        "capabilities.lambda_uses");
  test "a capability parameter adds to an associated capability set" (fun () ->
      let folded = Fixtures.Capabilities.folded in
      fine (feed ^ folded ^ Fixtures.Capabilities.capability_parameter_adds_to_an_associated);
      one_diagnostic
        (feed ^ folded ^ Fixtures.Capabilities.capability_parameter_adds_to_an_associated_2)
        "capabilities.not_available");
  test "an any value hides only a type whose associated capability sets are empty" (fun () ->
      fine (feed ^ Fixtures.Capabilities.any_value_hides_only_a_type_whose_associated);
      one_diagnostic
        (feed ^ Fixtures.Capabilities.any_value_hides_only_a_type_whose_associated_2)
        "types.no_impl";
      one_diagnostic
        (feed ^ Fixtures.Capabilities.any_value_hides_only_a_type_whose_associated_3)
        "types.no_impl")

let check packages =
  Database.For_testing.list_diagnostics [ Resolve; Interface; Infer ] (Support.database packages)

let one_diagnostic = Support.one_diagnostic ~check
let fine text = Support.no_diagnostics ~check [ ("app::main", text) ]

let () =
  Harness.test "a capability call needs its capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.clock_call_without_uses "capabilities.not_available");
  Harness.test "a function that declares a capability may call it" (fun () ->
      fine Fixtures.Capabilities.clock_call_using_clock);
  Harness.test "a call to a function with uses needs its capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.call_of_stamp "capabilities.not_available");
  Harness.test "provide makes a capability available in its block" (fun () ->
      fine Fixtures.Capabilities.provide_of_a_fixed_clock);
  Harness.test "provide records each capability's impl with its generic arguments" (fun () ->
      let text = Fixtures.Capabilities.provide_of_a_generic_fixed_clock in
      let packages = Support.setup [ ("app::main", text) ] in
      let key : Resolve.Names.key =
        {
          module_ = Support.module_of "app::main";
          path = Top { module_ = Support.module_of "app::main"; name = "f" };
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
          (Support.core_nodes packages key).expressions
      with
      | [ [ [ { capability; impl = Impl _; arguments = [ (_, Type tag) ] } ] ] ]
        when Path.equal capability (Support.top "standard::capabilities" "Clock")
             && Types.show tag = "Bool" ->
          ()
      | _ -> Harness.fail "not recorded");
  Harness.test "a specification may not use Panic" (fun () ->
      one_diagnostic Fixtures.Capabilities.ensures_calling_checked_using_panic
        "capabilities.not_available");
  Harness.test "a specification cannot use the function's capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.ensures_calling_stamp "capabilities.not_available");
  Harness.test "a loop invariant cannot use the function's capabilities" (fun () ->
      one_diagnostic Fixtures.Capabilities.loop_invariant_calling_stamp "capabilities.not_available");
  Harness.test "a type's invariant may use no capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.invariant_calling_stamp "capabilities.not_available");
  Harness.test "a law may use no capability" (fun () ->
      one_diagnostic Fixtures.Capabilities.law_calling_stamp "capabilities.not_available");
  Harness.test "a parallel branch has only Panic" (fun () ->
      one_diagnostic Fixtures.Capabilities.clock_call_in_a_parallel_branch
        "capabilities.not_available");
  Harness.test "a lambda's uses must fit the function type it is passed as" (fun () ->
      one_diagnostic Fixtures.Capabilities.lambda_using_clock_passed_as_plain
        "capabilities.lambda_uses");
  Harness.test "a loop over a value needs the capabilities that its `element` uses" (fun () ->
      one_diagnostic Fixtures.Capabilities.loop_over_a_ticker_without_uses
        "capabilities.not_available");
  Harness.test "a loop over a value can use the function's capabilities" (fun () ->
      fine Fixtures.Capabilities.loop_over_a_ticker_using_clock);
  Harness.test
    "a capability parameter is instantiated with the capabilities of the lambdas passed for it"
    (fun () -> fine Fixtures.Capabilities.for_each_of_lambdas);
  Harness.test "a trait's method solves its capability parameter as a function does" (fun () ->
      let visitor = Fixtures.Capabilities.visitor in
      let call =
        "{\n  numbers.visit_all(fn(value) {\n    let _ = Clock.now()\n    let _ = value\n  })\n}\n"
      in
      fine (visitor ^ "fn f(numbers: Numbers)\n  uses Clock\n" ^ call);
      one_diagnostic (visitor ^ "fn f(numbers: Numbers)\n" ^ call) "capabilities.not_available");
  Harness.test "a capability parameter's set must be available at the call" (fun () ->
      one_diagnostic Fixtures.Capabilities.for_each_of_a_lambda_using_clock
        "capabilities.not_available");
  Harness.test "a test has Panic" (fun () -> fine Fixtures.Capabilities.test_calling_panic);
  Harness.test "a place whose implementation mutates state is provided mut" (fun () ->
      one_diagnostic Fixtures.Capabilities.counter_provided_as_tally "capabilities.provide_mode")

let () =
  Harness.test "a dependency can use only the capabilities that it is granted" (fun () ->
      let packages =
        Support.setup
          [
            ("app::main", Fixtures.Capabilities.call_of_a_dependencys_stamp);
            ("clock_library::time", Fixtures.Capabilities.time_stamp_using_clock);
          ]
      in
      let packages =
        Support.with_dependencies packages { owner = None; name = "app" }
          [ { package = { owner = None; name = "clock_library" }; capabilities = [] } ]
      in
      match Support.codes (check packages (Support.file_of "app::main")) with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  let with_grant files granted =
    let packages =
      Support.with_dependencies (Support.setup files) { owner = None; name = "app" }
        [ { package = { owner = None; name = "clock_library" }; capabilities = granted } ]
    in
    Support.codes (check packages (Support.file_of "app::main"))
  in
  let library = ("clock_library::time", Fixtures.Capabilities.library_time) in
  Harness.test "a dependency's trait method can use only the granted capabilities" (fun () ->
      match with_grant [ ("app::main", Fixtures.Capabilities.wall_stamp_call); library ] [] with
      | "capabilities.not_granted" :: _ -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "a dependency's trait method can use a granted capability" (fun () ->
      match
        with_grant [ ("app::main", Fixtures.Capabilities.wall_stamp_call); library ] [ "Clock" ]
      with
      | [] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual));
  Harness.test "providing a dependency's type checks the grants for the capabilities of its impls"
    (fun () ->
      match
        with_grant
          [ ("app::main", Fixtures.Capabilities.provide_of_a_dependencys_fixed_clock); library ]
          []
      with
      | [ "capabilities.not_granted" ] -> ()
      | actual -> Harness.fail "found [%s]" (String.concat "; " actual))

let () =
  Harness.test "an implementation of a capability may not call the capability directly" (fun () ->
      one_diagnostic Fixtures.Capabilities.notes_impl_calling_notes "capabilities.not_available");
  Harness.test "an implementation of a capability may hand the capability to a function value"
    (fun () -> fine Fixtures.Capabilities.notes_impl_handing_notes_to_a_function)

let codes_with_grants files grants =
  let packages =
    Support.with_dependencies
      (Support.setup ~dependencies:[ ("plugins", "framework") ] files)
      { owner = None; name = "app" }
      (List.map (fun (package, capabilities) -> { Manifest.package; capabilities }) grants)
  in
  (packages, Support.codes (check packages (Support.file_of "app::main")))

let expect_codes ~expected (_, actual) =
  if actual <> expected then
    Harness.fail "found [%s], expected [%s]" (String.concat "; " actual)
      (String.concat "; " expected)

let time = ("clock_library::time", Fixtures.Capabilities.time_stamp_using_clock)
let sources = ("framework::sources", Fixtures.Capabilities.sources_sources)
let timers = ("plugins::timers", Fixtures.Capabilities.timers_timers)

let () =
  let value = ("app::main", Fixtures.Capabilities.dependencys_function_as_a_value) in
  Harness.test "a function value of a dependency's function can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ value; time ] [ ({ owner = None; name = "clock_library" }, []) ]));
  Harness.test "a function value of a dependency's function can use a granted capability" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ value; time ]
           [ ({ owner = None; name = "clock_library" }, [ "Clock" ]) ]));
  let bound = ("app::main", Fixtures.Capabilities.bound) in
  Harness.test
    "an impl of a dependency that satisfies a bound can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]));
  Harness.test "an impl of a dependency that satisfies a bound can use a granted capability"
    (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ bound; sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, [ "Clock" ]);
           ]));
  Harness.test "an impl of a dependency behind an `any` value can use only the granted capabilities"
    (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants
           [ ("app::main", Fixtures.Capabilities.any_timer_from_plugins); sources; timers ]
           [
             ({ owner = None; name = "framework" }, [ "Clock" ]);
             ({ owner = None; name = "plugins" }, []);
           ]))

let ledger = ("store::ledger", Fixtures.Capabilities.ledger_ledger)
let pays = ("app::main", Fixtures.Capabilities.pays)

let problems packages =
  let app : Path.package = { owner = None; name = "app" } in
  let database = Support.database packages in
  Database.check database [ app ];
  Database.list_manifest_problems database app

let () =
  Harness.test "a grant names a capability outside the prelude by its full path" (fun () ->
      expect_codes ~expected:[]
        (codes_with_grants [ pays; ledger ]
           [ ({ owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]));
  Harness.test "a capability's name alone grants only one of the prelude" (fun () ->
      let packages, actual =
        codes_with_grants [ pays; ledger ] [ ({ owner = None; name = "store" }, [ "Ledger" ]) ]
      in
      expect_codes ~expected:[ "capabilities.not_granted" ] (packages, actual);
      match problems packages with
      | [ Not_a_capability { dependency = { Path.owner = None; name = "store" }; name = "Ledger" } ]
        ->
          ()
      | _ -> Harness.fail "the grant is not reported");
  Harness.test "a grant covers only the capabilities it names" (fun () ->
      expect_codes ~expected:[ "capabilities.not_granted" ]
        (codes_with_grants [ pays; ledger ]
           [ ({ Path.owner = None; name = "store" }, [ "Clock" ]) ]))

let () =
  Harness.test "a dependency that nothing in the package names is reported" (fun () ->
      let packages, _ =
        codes_with_grants
          [ ("app::main", Fixtures.Capabilities.function_returning_one); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      match problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "a dependency named in a path is used" (fun () ->
      let packages, _ =
        codes_with_grants [ pays; ledger ]
          [ ({ Path.owner = None; name = "store" }, [ "store::ledger::Ledger" ]) ]
      in
      if problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency whose trait's method is called with a dot is used" (fun () ->
      let packages, actual =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.call_of_doubled);
            ("shapes::sizes", Fixtures.Capabilities.doubled_trait_for_int64);
          ]
          [ ({ Path.owner = None; name = "shapes" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      if problems packages <> [] then Harness.fail "reported");
  Harness.test "an unused dependency is reported for every kind of definition in the package"
    (fun () ->
      let packages, actual =
        codes_with_grants
          [ ("app::main", Fixtures.Capabilities.package_of_every_kind_of_definition); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      match problems packages with
      | [ Unused_dependency { Path.owner = None; name = "clock_library" } ] -> ()
      | _ -> Harness.fail "not reported");
  Harness.test "an unused dependency is not reported for a package with an error" (fun () ->
      let packages, _ =
        codes_with_grants
          [ ("app::main", Fixtures.Capabilities.function_returning_true_as_int64); time ]
          [ ({ Path.owner = None; name = "clock_library" }, []) ]
      in
      if problems packages <> [] then Harness.fail "reported");
  Harness.test "a dependency that only a test uses is left out of the code's packages" (fun () ->
      let shapes : Path.package = { owner = None; name = "shapes" }
      and limits : Path.package = { owner = None; name = "limits" } in
      let packages, actual =
        codes_with_grants
          [
            ("app::main", Fixtures.Capabilities.doubling_with_a_test_of_bounds);
            ("shapes::sizes", Fixtures.Capabilities.doubled_trait_for_int64);
            ("limits::bounds", Fixtures.Capabilities.bounds_most);
          ]
          [ (shapes, []); (limits, []) ]
      in
      expect_codes ~expected:[] (packages, actual);
      if problems packages <> [] then Harness.fail "a dependency is reported unused";
      match
        Database.list_code_packages (Support.database packages) { owner = None; name = "app" }
      with
      | Some code_packages when List.mem shapes code_packages && not (List.mem limits code_packages)
        ->
          ()
      | Some code_packages ->
          Harness.fail "found [%s]" (String.concat "; " (List.map Path.show_package code_packages))
      | None -> Harness.fail "the code's packages are not computed")

let ticks = Fixtures.Capabilities.ticks

let () =
  Harness.test "a function that uses a capability is not passed as one that uses none" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.tick_passed_without_uses) "types.mismatch");
  Harness.test "a function that uses a capability is not bound as one that uses none" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.tick_bound_without_uses) "types.mismatch");
  Harness.test "a function that uses a capability is not returned as one that uses none" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.tick_returned_without_uses) "types.mismatch");
  Harness.test "a function that uses a capability is not stored as one that uses none" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.tick_stored_without_uses) "types.mismatch");
  Harness.test "a function that uses a capability is not assigned as one that uses none" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.tick_assigned_without_uses) "types.mismatch");
  Harness.test "function types inside a type must list the same capabilities" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.list_of_actions_losing_uses) "types.mismatch");
  Harness.test "a function that uses nothing is passed as one that may use a capability" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.still_bound_using_clock));
  Harness.test "a branch's function meets the function type expected of the branches" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.branches_of_functions_using_clock));
  Harness.test "a branch's function that uses a capability is not bound as one that uses none"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.branches_of_functions_bound_without_uses)
        "types.mismatch");
  Harness.test
    "a capability parameter is instantiated with the capabilities of the functions passed for it"
    (fun () -> fine (ticks ^ Fixtures.Capabilities.each_time_of_tick_using_clock));
  Harness.test "the capabilities of a function passed for a capability parameter must be available"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_tick_without_uses)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a parenthesized lambda"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_parenthesized_lambda)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a function in a branch"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_branch_of_functions)
        "capabilities.not_available");
  Harness.test
    "a capability parameter is instantiated with the capabilities of a lambda in a branch"
    (fun () ->
      one_diagnostic
        (ticks ^ Fixtures.Capabilities.each_time_of_a_branch_with_a_lambda)
        "capabilities.not_available");
  Harness.test "a function passes its own capability parameter on" (fun () ->
      fine (ticks ^ Fixtures.Capabilities.passes_on_its_own_capability));
  Harness.test "a function's own capability parameter is rigid in a lambda's type" (fun () ->
      one_diagnostic Fixtures.Capabilities.own_capability_given_a_lambda_using_clock
        "capabilities.lambda_uses");
  Harness.test "a function's own capability parameter is rigid in a binding's type" (fun () ->
      one_diagnostic (ticks ^ Fixtures.Capabilities.own_capability_given_tick) "types.mismatch");
  Harness.test "a function calls itself with its own capability parameter" (fun () ->
      fine Fixtures.Capabilities.repeat_passing_its_own_capability);
  Harness.test "a recursive call needs the capabilities that it passes for its capability parameter"
    (fun () ->
      let repeat uses =
        ticks
        ^ "fn repeat[capability Mine](action: (fn() -> Instant uses Mine), again: Bool) -> Instant\n\
          \  uses " ^ uses
        ^ "\n{\n  if again {\n    repeat(tick, again: false)\n  } else {\n    action()\n  }\n}\n"
      in
      one_diagnostic (repeat "Mine") "capabilities.not_available";
      fine (repeat "Mine, Clock"))

let later = ticks ^ Fixtures.Capabilities.later

let () =
  Harness.test "a call's result has the capabilities that were passed for the capability parameter"
    (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.later_of_tick_without_uses)
        "capabilities.not_available";
      fine (later ^ Fixtures.Capabilities.later_of_tick_using_clock);
      fine (later ^ Fixtures.Capabilities.later_of_still));
  Harness.test "a call's result must fit the function type that it is checked against" (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.later_of_tick_bound_without_uses)
        "types.mismatch";
      fine (later ^ Fixtures.Capabilities.later_of_tick_bound_using_clock));
  Harness.test "a call's result may widen to more `uses` without requiring them at the call"
    (fun () -> fine (ticks ^ Fixtures.Capabilities.checked_result_widened));
  Harness.test "a variable that is assigned a second function has the capabilities of both"
    (fun () ->
      one_diagnostic
        (later ^ Fixtures.Capabilities.held_still_then_tick_without_uses)
        "capabilities.not_available";
      fine (later ^ Fixtures.Capabilities.held_still_then_tick_using_clock));
  Harness.test "a type and a trait cannot take a capability parameter" (fun () ->
      one_diagnostic "type Holder[capability Granted](action: (fn() -> Instant uses Granted))\n"
        "types.misplaced_capability_parameter";
      one_diagnostic Fixtures.Capabilities.trait_with_a_capability_parameter
        "types.misplaced_capability_parameter";
      fine "type Holder(action: (fn() -> Instant uses Clock))\n")

let widenings text =
  List.length
    (List.filter
       (fun (node : Core.expression) ->
         match node.kind with Convert { conversion = Widen; _ } -> true | _ -> false)
       (Support.first_core_nodes text).expressions)

let () =
  Harness.test "a function bound as a type that promises a cost leaves the cost to the prover"
    (fun () ->
      match widenings Fixtures.Capabilities.forever_bound_as_finite with
      | 1 -> ()
      | actual -> Harness.fail "%d conversions" actual);
  Harness.test "a function that promises to end can be bound as one that does" (fun () ->
      fine Fixtures.Capabilities.quick_bound_as_finite);
  Harness.test "function types inside a type must promise the same costs" (fun () ->
      one_diagnostic Fixtures.Capabilities.list_of_actions_gaining_a_cost "types.mismatch")

let readings = Fixtures.Capabilities.readings

let () =
  Harness.test "the next of a cursor needs the capabilities in its `Uses`" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.next_of_readings_without_uses)
        "capabilities.not_available");
  Harness.test "the next of a cursor is fine where its `Uses` are available" (fun () ->
      fine (readings ^ Fixtures.Capabilities.next_of_readings_using_meter));
  Harness.test "a for loop over a cursor needs the capabilities in the cursor's `Uses`" (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.for_loop_over_readings)
        "capabilities.not_available");
  Harness.test "a cursor whose `next` uses a capability meets a Cursor bound" (fun () ->
      fine (readings ^ Fixtures.Capabilities.pull_from_readings_using_meter));
  Harness.test "a generic function that advances a cursor needs the cursor's capabilities"
    (fun () -> one_diagnostic Fixtures.Capabilities.pull_without_uses "capabilities.not_available");
  Harness.test "a call that passes a cursor needs the capabilities in the cursor's `Uses`"
    (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.pull_from_readings)
        "capabilities.not_available");
  Harness.test "a method that Cursor provides needs the capabilities in the cursor's `Uses`"
    (fun () ->
      one_diagnostic
        (readings ^ Fixtures.Capabilities.count_of_readings_without_uses)
        "capabilities.not_available");
  Harness.test "a method that Cursor provides runs where the cursor's `Uses` are available"
    (fun () -> fine (readings ^ Fixtures.Capabilities.count_of_readings_using_meter));
  Harness.test "a cursor whose `next` uses no capability needs none" (fun () ->
      fine Fixtures.Capabilities.counted_cursor);
  Harness.test "a cursor whose `next` uses a capability cannot be an any value" (fun () ->
      one_diagnostic (readings ^ Fixtures.Capabilities.any_cursor_of_readings) "types.no_impl")

let feed = Fixtures.Capabilities.feed

let () =
  Harness.test "an impl that leaves out an associated capability set has the empty set" (fun () ->
      fine (feed ^ Fixtures.Capabilities.drain_of_a_counter));
  Harness.test "a call needs the capabilities of the set that the impl defines" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.drain_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a provided method needs the capabilities of the set that the impl defines"
    (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.skip_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a set defined from a parameter's set is the argument's set" (fun () ->
      fine (feed ^ Fixtures.Capabilities.twice_of_a_gauge_using_meter);
      one_diagnostic
        (feed ^ Fixtures.Capabilities.twice_of_twice_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a method of an impl can use only the set that the impl defines" (fun () ->
      one_diagnostic (feed ^ Fixtures.Capabilities.greedy_feed_pull_using_meter) "types.impl_uses");
  Harness.test "an impl defines only a set that its trait declares, and only once" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.impl_defining_an_undeclared_set)
        "types.extra_member";
      one_diagnostic (feed ^ Fixtures.Capabilities.impl_defining_uses_twice) "types.extra_member");
  Harness.test "a set cannot be defined from itself" (fun () ->
      one_diagnostic
        (feed ^ Fixtures.Capabilities.set_defined_as_itself)
        "types.unknown_associated_capability");
  Harness.test "an associated capability set is of a trait that declares it" (fun () ->
      one_diagnostic Fixtures.Capabilities.trait_using_an_undeclared_set
        "types.unknown_associated_capability";
      one_diagnostic Fixtures.Capabilities.unbounded_parameters_set
        "types.unknown_associated_capability";
      one_diagnostic Fixtures.Capabilities.self_set_outside_a_trait "types.misplaced_self_type";
      one_diagnostic Fixtures.Capabilities.set_of_an_unknown_name "resolve.not_a_generic_parameter";
      one_diagnostic Fixtures.Capabilities.set_of_a_capability_parameter
        "types.unknown_associated_type");
  Harness.test "a trait's methods can use a set that a required trait declares" (fun () ->
      let rewind = Fixtures.Capabilities.rewind in
      fine (feed ^ rewind ^ Fixtures.Capabilities.rewind_of_a_gauge_using_meter);
      one_diagnostic
        (feed ^ rewind ^ Fixtures.Capabilities.back_twice_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "a function type can use an associated capability set" (fun () ->
      let apply = Fixtures.Capabilities.apply in
      fine (feed ^ apply ^ Fixtures.Capabilities.apply_to_a_gauge);
      one_diagnostic
        (feed ^ apply ^ Fixtures.Capabilities.apply_to_a_counter_using_meter)
        "capabilities.lambda_uses");
  Harness.test "a capability parameter adds to an associated capability set" (fun () ->
      let folded = Fixtures.Capabilities.folded in
      fine (feed ^ folded ^ Fixtures.Capabilities.fold_of_a_counter_using_meter);
      one_diagnostic
        (feed ^ folded ^ Fixtures.Capabilities.fold_of_a_gauge_without_uses)
        "capabilities.not_available");
  Harness.test "an any value hides only a type whose associated capability sets are empty"
    (fun () ->
      fine (feed ^ Fixtures.Capabilities.any_feed_of_a_counter);
      one_diagnostic (feed ^ Fixtures.Capabilities.any_feed_of_a_gauge) "types.no_impl";
      one_diagnostic (feed ^ Fixtures.Capabilities.any_feed_of_a_generic_source) "types.no_impl")
